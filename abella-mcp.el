;; Copyright (C) 2026  Nathan Guermond
;; SPDX-License-Identifier: GPL-3.0-or-later
;; Version 0.1.1

;; Interactive Abella proof checking via abella_mcp.
;;
;; abella_mcp is an MCP server (newline-delimited JSON-RPC 2.0 over
;; stdio) that drives Abella as a background subprocess and multiplexes
;; any number of independent sessions over that one connection.
;; One shared abella_mcp process is
;; started lazily and reused for every abella-mode buffer; each buffer
;; gets its own session_id, so files run independently of one another.
;;
;; Each buffer tracks a "locked position": the buffer position up to
;; which text has actually been sent to its session, alongside a stack
;; of markers, one per individual command that succeeded, used to
;; retract by an exact number of `undo.'s. It is shown in the fringe as
;; a single marker (via `overlay-arrow-variable-list'), not by
;; highlighting the whole region, and editing text before it retracts
;; the session back to the last command still before the edit.

(require 'json)
(require 'cl-lib)

;; ------------------------------------------------------------------
;; The shared abella_mcp process
;; ------------------------------------------------------------------

(defvar abella-mcp-executable
  (or (executable-find "abella_mcp")
      (car (file-expand-wildcards "~/.opam/*/bin/abella_mcp")))
  "Path to the abella_mcp executable.
Resolved from PATH first (as `executable-find' sees it, which may
differ from an interactive shell's PATH -- e.g. it may be missing an
opam switch's bin directory), then an opam switch directly, then the
dev build tree as a last resort.")

(defvar abella-mcp-abella-bin
  (or (executable-find "abella")
      (car (file-expand-wildcards "~/.opam/*/bin/abella")))
  "Path to the `abella' binary, passed to abella_mcp as ABELLA_BIN.
Emacs's PATH may not include an opam switch's bin directory even when
an interactive shell's does, so this is resolved explicitly instead of
relying on abella_mcp's own PATH search.")

(defvar abella-mcp--process nil)
(defvar abella-mcp--output "")
(defvar abella-mcp--id-counter 0)

(defun abella-mcp--filter (_proc chunk)
  (setq abella-mcp--output (concat abella-mcp--output chunk)))

(defun abella-mcp--ensure-process ()
  (unless (process-live-p abella-mcp--process)
    (unless (and abella-mcp-executable (file-executable-p abella-mcp-executable))
      (error "abella-mcp executable not found: %s" abella-mcp-executable))
    (setq abella-mcp--output "")
    (let ((process-environment
           (if abella-mcp-abella-bin
               (cons (concat "ABELLA_BIN=" abella-mcp-abella-bin) process-environment)
             process-environment)))
      (setq abella-mcp--process
            (make-process
             :name "abella-mcp"
             :command (list abella-mcp-executable)
             :connection-type 'pipe
             :noquery t
             :coding 'utf-8
             :filter #'abella-mcp--filter
             :stderr (get-buffer-create " *abella-mcp-log*"))))
    (abella-mcp--request "initialize" '((protocolVersion . "2024-11-05")) 10)))

(defun abella-mcp--read-line (timeout)
  "Block until a full line is available, or TIMEOUT seconds pass."
  (let ((deadline (+ (float-time) timeout)))
    (while (and (not (string-match "\n" abella-mcp--output))
                (< (float-time) deadline)
                (process-live-p abella-mcp--process))
      (accept-process-output abella-mcp--process 0.2))
    (when (string-match "\n" abella-mcp--output)
      (prog1 (substring abella-mcp--output 0 (match-beginning 0))
        (setq abella-mcp--output (substring abella-mcp--output (match-end 0)))))))

(defun abella-mcp--request (method params &optional timeout)
  "Send METHOD/PARAMS as a JSON-RPC request and return the decoded
response alist. PARAMS is an alist, or nil to omit the params field.

Waits specifically for a response whose id matches this request,
discarding any earlier line that doesn't -- if a previous call was
abandoned via \\[keyboard-quit] while still waiting, its response can
arrive late and sit unread; without this, a later call could pick that
stale line up and mistake it for its own answer."
  (abella-mcp--ensure-process)
  (setq abella-mcp--id-counter (1+ abella-mcp--id-counter))
  (let* ((id abella-mcp--id-counter)
         (base `((jsonrpc . "2.0") (id . ,id) (method . ,method)))
         (full (if params (append base (list (cons 'params params))) base))
         (payload (json-serialize full))
         (deadline (+ (float-time) (or timeout 30))))
    (process-send-string abella-mcp--process (concat payload "\n"))
    (let (resp)
      (while (not resp)
        (let* ((remaining (- deadline (float-time)))
               (line (and (> remaining 0) (abella-mcp--read-line remaining))))
          (unless line
            (error "abella-mcp: timed out waiting for a response to %s" method))
          (let ((parsed (ignore-errors
                          (json-parse-string line :object-type 'alist :array-type 'list))))
            (when (and parsed (equal (alist-get 'id parsed) id))
              (setq resp parsed)))))
      resp)))

(defun abella-mcp-call-tool (name arguments &optional timeout)
  "Call the abella_mcp tool NAME with ARGUMENTS (an alist).
Returns (TEXT . IS-ERROR)."
  (let* ((resp (abella-mcp--request "tools/call"
                                     `((name . ,name) (arguments . ,arguments))
                                     timeout))
         (err (alist-get 'error resp)))
    (if err
        (cons (format "abella-mcp error: %s" (alist-get 'message err)) t)
      (let* ((result (alist-get 'result resp))
             (content (alist-get 'content result))
             (text (alist-get 'text (car content)))
             (is-error (eq (alist-get 'isError result) t)))
        (cons (or text "") is-error)))))

;; ------------------------------------------------------------------
;; Per-buffer session state
;; ------------------------------------------------------------------

(defvar-local abella-session-id nil
  "This buffer's abella_mcp session_id, assigned on first use.")

(defvar-local abella-session-started nil
  "Non-nil once abella_start has been called for `abella-session-id'
in this Emacs session.")

(defvar-local abella-checkpoints nil
  "Markers, most recent first, one per Abella command that has
succeeded, at the buffer position right after it.")

;; A single fringe marker at the locked position, via Emacs's standard
;; overlay-arrow facility (the same mechanism Proof General and gud use
;; for "point reached so far") rather than highlighting the whole region.
(defvar-local abella-locked-marker nil
  "Marker shown in the fringe at the position up to which this
buffer's text has been sent to Abella.")

(add-to-list 'overlay-arrow-variable-list 'abella-locked-marker)

(defun abella-locked-position ()
  (if abella-checkpoints (marker-position (car abella-checkpoints)) (point-min)))

(defvar abella--suppress-goto nil
  "Bound to t while retracting from `abella--on-change', so a mid-edit
auto-retraction doesn't yank point away from where you're typing.")

;; Adapted from `proof-set-overlay-arrow' in GNU Proof General
;; (generic/proof-script.el), whose copyright notice reads:
;;   Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;;   Portions © Copyright 2003-2021  Free Software Foundation, Inc.
;;   Portions © Copyright 2001-2017  Pierre Courtieu
;;   Portions © Copyright 2010, 2016  Erik Martin-Dorel
;;   Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;;   Portions © Copyright 2015-2017  Clément Pit-Claudel
;; Used under the terms of the GNU General Public License, version 3
;; or later (SPDX-License-Identifier: GPL-3.0-or-later).
(defun abella--arrow-position (pos)
  "Normalize POS to a beginning-of-line position for the fringe arrow,
mirroring Proof General's `proof-set-overlay-arrow'.  Our locked
position is normally mid-line -- right after the period ending a
command, not the start of the next line -- and that only happens to
coincide with beginning-of-line for POS = (point-min); everywhere else
the arrow needs a bol position to render reliably."
  (save-excursion
    (goto-char pos)
    (skip-chars-forward " \t\n")
    (unless (eq (point) (point-max))
      (beginning-of-line))
    (point)))

(defun abella--update-locked-marker ()
  (let ((pos (abella-locked-position)))
    (unless (markerp abella-locked-marker)
      (setq abella-locked-marker (make-marker)))
    (set-marker abella-locked-marker (abella--arrow-position pos) (current-buffer))
    (unless abella--suppress-goto
      (goto-char pos)
      ;; gud.el's overlay-arrow (the same mechanism we use) never
      ;; relies on `goto-char' alone -- it always also calls
      ;; `set-window-point' on the displaying window. Our own moves
      ;; happen around a blocking network round trip to abella_mcp,
      ;; which is exactly the kind of gap where window-point and
      ;; buffer-point can drift apart and the fringe arrow silently
      ;; stops following, even though `(point)' itself is correct.
      (dolist (win (get-buffer-window-list (current-buffer) nil t))
        (set-window-point win pos)))))

(defun abella--on-change (beg _end _len)
  "If an edit touches text at or before the locked position, the
buffer no longer matches what Abella actually has, so retract back to
the last command still before the edit and move the marker there."
  (when (and abella-checkpoints (< beg (abella-locked-position)))
    (let ((abella--suppress-goto t))
      (abella--display-result (abella-retract-to beg)))))

(defun abella-mcp-setup ()
  (add-hook 'after-change-functions #'abella--on-change nil t)
  ;; `overlay-arrow-string' is a single global variable; real Coq
  ;; buffers via proof-general blank it out (custom-modes.el sets it
  ;; globally to ""), which would otherwise silently hide this marker
  ;; too. Make it buffer-local here so abella buffers always show it.
  (setq-local overlay-arrow-string "=>")
  (setq-local abella-subgoal-depth-function #'abella--subgoal-depth-at)
  (abella--update-locked-marker))

(add-hook 'abella-mode-hook #'abella-mcp-setup)

(defun abella-session-name ()
  (format "emacs-%s-%d"
          (file-name-base (or (buffer-file-name) (buffer-name)))
          (random 1000000)))

(defun abella-output-buffer-name ()
  (format "*abella:%s*" (file-name-nondirectory (or (buffer-file-name) (buffer-name)))))

(define-derived-mode abella-output-mode special-mode "Abella-Output"
  "Mode for displaying Abella proof state and command output."
  (setq-local font-lock-defaults '(abella-font-lock-keywords)))

(defun abella-show-output (text &optional scroll-to-top)
  "Display TEXT in this buffer's Abella output buffer.
Scrolls to the end by default (useful for a command transcript, where
the latest entry is what matters), or to the top if SCROLL-TO-TOP is
non-nil (useful for a full proof state, which should be read from its
first hypothesis down)."
  (let* ((buf (get-buffer-create (abella-output-buffer-name)))
         (pos (if scroll-to-top (point-min) (point-max))))
    (with-current-buffer buf
      (unless (derived-mode-p 'abella-output-mode) (abella-output-mode))
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert text)
        (goto-char pos)))
    ;; The output window is usually not the selected window, so moving
    ;; the buffer's own point isn't enough to scroll it into view --
    ;; that window tracks its own point independently until selected.
    (let ((window (display-buffer buf '(display-buffer-reuse-window
                                         (inhibit-same-window . t)))))
      (when window (set-window-point window pos)))))

(defun abella-ensure-session ()
  "Return this buffer's session_id, starting it via abella_start if
this is the first use in this Emacs session."
  (unless abella-session-id (setq abella-session-id (abella-session-name)))
  (unless abella-session-started
    (let* ((cwd (and (buffer-file-name) (file-name-directory (buffer-file-name))))
           (args (if cwd `((session_id . ,abella-session-id) (cwd . ,cwd))
                   `((session_id . ,abella-session-id)))))
      (let ((result (abella-mcp-call-tool "abella_start" args)))
        (setq abella-session-started t)
        (abella-show-output (car result)))))
  abella-session-id)

(defun abella--session-missing-p (text)
  (string-match-p "No Abella session" text))

;; ------------------------------------------------------------------
;; Sending buffer text
;; ------------------------------------------------------------------

(defun abella-split-commands (from to)
  "Return the list of end positions of each top-level (period-
terminated) command in [FROM, TO), in buffer order."
  (save-excursion
    (goto-char from)
    (let (positions)
      (while (re-search-forward "\\." to t)
        (when (abella-top-level-p (match-beginning 0))
          (push (point) positions)))
      (nreverse positions))))

(defun abella-mcp--count-transcript-entries (text)
  "Count the '> cmd' entries in a collapse=false abella_send transcript."
  (let ((count 0) (start 0))
    (while (string-match "^> " text start)
      (setq count (1+ count))
      (setq start (match-end 0)))
    count))

(defvar-local abella--last-state nil
  "The most recently fetched proof state text, cached so indentation
(see `abella--subgoal-depth-at') can read the current subgoal depth
without a network round trip on every TAB press. Stays correct as
long as it is refreshed here whenever the locked position changes.")

(defun abella-fetch-state ()
  "Return the full current proof state for this buffer's session (or
top-level status if no proof is open), via abella_state -- the full
state rather than a delta, and with no command transcript attached."
  (setq abella--last-state
        (car (abella-mcp-call-tool "abella_state" `((session_id . ,abella-session-id))))))

(defun abella--top-level-state-p (state-text)
  (string-prefix-p "(no proof state; at top level)" state-text))

(defun abella--depth-from-state (state)
  "Parse a \"Subgoal N.N.N\" header out of STATE into a nesting depth
(1 for a lone/first pending subgoal, one more per dot), or nil if
STATE is nil or reports the top level rather than an open proof."
  (when (and state (not (abella--top-level-state-p state)))
    (if (string-match "\\`Subgoal \\([0-9]+\\(\\.[0-9]+\\)*\\)" state)
        (1+ (cl-count ?. (match-string 1 state)))
      1)))

(defun abella--sync-to (pos)
  "Make the session's cached state reflect being caught up exactly
through POS: retract first if it has already advanced past POS (so
re-indenting an already-processed region gives the same answer every
time, instead of looking \"retroactive\" and defaulting to 0 just
because the session has since moved on), then advance through
whatever gap remains.  Done silently -- without moving point or
displaying more than a real step/retract would.  Returns the resulting
state text, or nil if that isn't achievable (advancing hit an error)."
  (let ((abella--suppress-goto t))
    (when (< pos (abella-locked-position))
      (abella--display-result (abella-retract-to pos)))
    (let ((locked (abella-locked-position)))
      (if (= locked pos)
          abella--last-state
        (let ((boundary (abella-find-top-level "\\." locked pos)))
          (if (not boundary)
              ;; POS is ahead of LOCKED only by whitespace/comments --
              ;; no new command actually stands between them, so the
              ;; cached state is still exactly right.
              abella--last-state
            (let ((result (abella-run-region locked boundary)))
              (abella--display-result result)
              (and (cdr result) (car result)))))))))

(defun abella--subgoal-depth-at (pos)
  "Return the session's subgoal nesting depth at POS, for
`abella-subgoal-depth-function', via `abella--sync-to'.  Returns nil
if that isn't achievable (a tactic error blocks progress -- \"stuck\")
or the resulting state is at the top level rather than mid-proof."
  (abella--depth-from-state (abella--sync-to pos)))

(defun abella--report (transcript-text)
  "Return (TEXT . IS-STATE): TRANSCRIPT-TEXT (from a send/undo) if we
are at the top level, where there is no proof state and the command
history is what's useful; otherwise the full current proof state,
which matters more than the transcript once inside a proof."
  (let ((state (abella-fetch-state)))
    (if (abella--top-level-state-p state)
        (cons transcript-text nil)
      (cons state t))))

(defun abella-run-region (from to &optional retried)
  "Send the Abella source in [FROM, TO) command by command, advancing
`abella-checkpoints' by however many actually succeeded. Returns
(TEXT . IS-STATE): the full proof state on success, or the failing
command's transcript entry (IS-STATE nil) on error. RETRIED guards the
one-shot session-recovery retry below against looping forever if
starting a session keeps failing."
  (let* ((session (abella-ensure-session))
         (positions (abella-split-commands from to))
         (n (length positions)))
    (if (= n 0)
        (cons "(nothing to send)" nil)
      (let* ((text (buffer-substring-no-properties from to))
             (result (abella-mcp-call-tool
                      "abella_send"
                      `((session_id . ,session) (commands . ,text) (collapse . :false))))
             (resp-text (car result))
             (is-error (cdr result)))
        (if (and is-error (not retried) (abella--session-missing-p resp-text))
            (progn
              (setq abella-session-started nil)
              (abella-ensure-session)
              (abella-run-region from to t))
          (let* ((shown (abella-mcp--count-transcript-entries resp-text))
                 (succeeded (min n (if is-error (max 0 (1- shown)) shown))))
            (dotimes (i succeeded)
              (push (copy-marker (nth i positions)) abella-checkpoints))
            (abella--update-locked-marker)
            ;; On error, the transcript is what shows which command
            ;; failed and why; on success, `abella--report' decides
            ;; between the transcript and the full state.
            (if is-error (cons resp-text nil) (abella--report resp-text))))))))

(defun abella-retract-to (target)
  "Retract to the last checkpoint at or before TARGET.
Tries a fast `abella_undo' first; Abella cannot undo back out of a
proof it has already completed, so on failure this falls back to
restarting the session and replaying every command from the start up
to TARGET, which always works. Returns (TEXT . IS-STATE) on success,
or nil if there was nothing to undo."
  (let ((session (abella-ensure-session))
        (popped nil))
    (while (and abella-checkpoints (> (marker-position (car abella-checkpoints)) target))
      (push (car abella-checkpoints) popped)
      (setq abella-checkpoints (cdr abella-checkpoints)))
    (if (not popped)
        nil
      (let* ((result (abella-mcp-call-tool
                       "abella_undo" `((session_id . ,session) (count . ,(length popped)))))
             (text (car result))
             (is-error (cdr result)))
        (dolist (m popped) (set-marker m nil))
        (if (not is-error)
            (progn (abella--update-locked-marker) (abella--report text))
          ;; Fast undo failed (e.g. it would cross a completed proof's
          ;; boundary): restart clean and replay up to TARGET instead.
          (dolist (m abella-checkpoints) (set-marker m nil))
          (setq abella-checkpoints nil)
          (setq abella-session-started nil)
          (abella-ensure-session)
          (abella--update-locked-marker)
          (if (<= target (point-min))
              (cons (abella-fetch-state) t)
            (abella-run-region (point-min) target)))))))

(defun abella--display-result (result)
  "Show RESULT, a (TEXT . IS-STATE) pair from `abella-run-region' or
`abella-retract-to', or nil if nothing happened."
  (if result
      (abella-show-output (car result) (cdr result))
    (abella-show-output "(nothing to undo)")))

;; ------------------------------------------------------------------
;; Interactive commands
;; ------------------------------------------------------------------

(defun abella-execute-to-cursor ()
  "Process (or retract to) the command boundary at or before point."
  (interactive)
  (let ((target (point))
        (locked (abella-locked-position)))
    (cond
     ((= target locked) (message "Already at the cursor."))
     ((< target locked)
      (abella--display-result (abella-retract-to target)))
     (t
      ;; `abella-find-top-level' returns the position right after the
      ;; matched period -- exactly the end boundary we want to send to.
      (let ((boundary (abella-find-top-level "\\." locked (1+ target))))
        (if (not boundary)
            (message "No complete command before point.")
          (abella--display-result (abella-run-region locked boundary))))))))

(defun abella-step-forward ()
  "Step to the next tactic or command."
  (interactive)
  (let* ((locked (abella-locked-position))
         (start (abella-find-first-top-level "\\." locked (point-max))))
    (if (not start)
        (message "No more commands to process.")
      (abella--display-result (abella-run-region locked (1+ start))))))

(defun abella-step-forward-command ()
  "Step to the next top-level command, running past the current
proof's remaining tactics (if any) to get there."
  (interactive)
  (let* ((locked (abella-locked-position))
         (next-kw (abella-find-first-top-level
                   abella-top-level-keyword-regexp locked (point-max)))
         (boundary
          (cond
           ((not next-kw) (point-max))
           ;; Nothing but blank/comment before the next keyword: we
           ;; haven't started that command yet, so run all of it (and
           ;; its proof, if any) and stop at the one after that.
           ((abella-blank-region-p locked next-kw)
            (or (abella-find-first-top-level
                 abella-top-level-keyword-regexp (1+ next-kw) (point-max))
                (point-max)))
           (t next-kw))))
    (if (<= boundary locked)
        (message "No more commands to process.")
      (abella--display-result (abella-run-region locked boundary)))))

(defun abella-undo-last ()
  "Undo the last tactic or command."
  (interactive)
  (if (not abella-checkpoints)
      (message "Nothing to undo.")
    (let ((prev (if (cdr abella-checkpoints)
                     (marker-position (cadr abella-checkpoints))
                   (point-min))))
      (abella--display-result (abella-retract-to prev)))))

(defun abella-retract-to-previous-command ()
  "Undo back to before the current top-level command."
  (interactive)
  (let* ((locked (abella-locked-position))
         (target (or (abella-find-last-top-level-start
                      abella-top-level-keyword-regexp (point-min) locked)
                     (point-min))))
    (abella--display-result (abella-retract-to target))))

(defun abella-kill-session ()
  "Stop this buffer's Abella session and reset all local tracking, so
the next command starts a fresh one from the top of the file.

If Emacs is currently blocked waiting on a response (e.g. a `search.'
that is taking a long time), this command is unreachable until you
first press \\[keyboard-quit] to abort that wait -- Emacs cannot
process a keybinding while a synchronous call is still running. Once
interrupted, run this to actually stop the (possibly still busy)
Abella subprocess.

Stopping the session itself is given a short timeout; if even that
does not respond, the shared abella_mcp connection is presumed wedged
and killed outright, which drops every buffer's session, not just
this one -- the only way out of a genuinely stuck pipe."
  (interactive)
  (when abella-session-id
    (condition-case _
        (abella-mcp-call-tool "abella_stop" `((session_id . ,abella-session-id)) 3)
      (error
       (message "abella-mcp is not responding; killing the shared process (this drops every session).")
       (when (process-live-p abella-mcp--process)
         (delete-process abella-mcp--process))
       (setq abella-mcp--process nil abella-mcp--output ""))))
  (dolist (m abella-checkpoints) (set-marker m nil))
  (setq abella-checkpoints nil)
  (setq abella-session-started nil)
  (abella--update-locked-marker)
  (message "Abella session %s stopped." abella-session-id))

(define-key abella-mode-keymap (kbd "C-c RET") #'abella-execute-to-cursor)
(define-key abella-mode-keymap (kbd "C-c C-f") #'abella-step-forward-command)
(define-key abella-mode-keymap (kbd "C-c C-n") #'abella-step-forward)
(define-key abella-mode-keymap (kbd "C-c C-p") #'abella-undo-last)
(define-key abella-mode-keymap (kbd "C-c C-b") #'abella-retract-to-previous-command)
(define-key abella-mode-keymap (kbd "C-c C-c") #'abella-kill-session)

(provide 'abella-mcp)
