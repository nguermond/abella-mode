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

(defvar-local abella--prompt "Abella"
  "This buffer's session's current Abella prompt: the name of the
theorem currently open, or \"Abella\" at the top level. Extracted from
the trailing \"[session: ID | prompt: PROMPT]\" tag abella_mcp attaches
to its own tool replies (`abella-mcp--strip-session-tag'), and shown as
one always-current header line in the output buffer
(`abella--update-session-tag') instead of repeated after every step.")

(defvar-local abella--session-tag-marker nil
  "Marker in the output buffer at the end of the single \"[session: ID
| prompt: PROMPT]\" header line `abella--update-session-tag' keeps up
to date there, or nil before that header has been created.")

(defvar-local abella-checkpoints nil
  "Markers, most recent first, one per Abella command that has
succeeded, at the buffer position right after it.")

;; ------------------------------------------------------------------
;; Structured session events
;; ------------------------------------------------------------------
;;
;; A persistent, append-only (except on retract) record of what this
;; buffer's session has actually processed: one event per top-level
;; command outside a proof (Kind/Type/Define/CoDefine/Import/
;; Specification/Set/Close/Query/...), or one event per whole
;; Theorem/Split -- its statement plus its entire proof script,
;; finalized only once the proof closes, not per-tactic. Kept in
;; lockstep with `abella-checkpoints' (advanced/retracted together, in
;; the same functions) so the two never drift apart.

(cl-defstruct (abella-event (:constructor abella-event-create))
  kind       ; the top-level keyword string, e.g. "Theorem", "Define", ...
  command    ; this event's own source text: a theorem's *statement*
             ;   only (not its proof script) for a Theorem/Split event,
             ;   the whole command otherwise
  status     ; 'ok or 'error
  raw        ; abella_mcp's own transcript chunk(s) for this event, its
             ;   command echo(es) and reply concatenated verbatim, in
             ;   order -- for a Theorem/Split event, its header's chunk
             ;   followed by every tactic's, through to closure
  warnings   ; list of strings detected by scanning `raw', e.g.
             ;   ("Proof completed via skip")
  start-marker   ; marker in the SOURCE buffer right after this event's
                 ;   own opening command (its header, for a Theorem/
                 ;   Split -- set as soon as `abella--pending-theorem'
                 ;   is created, before the proof closes) -- used only
                 ;   to tell whether a retract target falls before a
                 ;   still-*pending* theorem's own start (discard it,
                 ;   nothing to display was ever shown for it) or within
                 ;   it (leave it pending, untouched)
  source-marker  ; marker in the SOURCE buffer at this event's own end
                 ;   position (the last checkpoint it covers -- for a
                 ;   failed event, which never got a checkpoint of its
                 ;   own, wherever the last successful one already left
                 ;   off), so retracting a *finalized* event past it
                 ;   removes this event too
  output-marker) ; marker in the *abella:...* output buffer at the start
                 ;   of this event's own displayed text, so retracting
                 ;   past it can truncate the display to match

(defvar-local abella-events nil
  "Finalized session events, most recent first -- parallel to, and kept
in lockstep with, `abella-checkpoints'.")

(defvar-local abella--pending-theorem nil
  "The `abella-event' being built for a Theorem/Split whose proof is
currently open (its header, and every tactic's chunk/warnings
accumulated so far), or nil when not inside a proof. Finalized into
`abella-events' (and appended to the output buffer) once the proof
closes; discarded without ever being displayed if retracted past its
own start.")

(defun abella-mcp--split-transcript (text)
  "Split a collapse=false abella_send transcript TEXT into a list of
raw chunks, one per \"> \"-prefixed entry, in order: the text from
right after that entry's own \"> \" through (but not including) the
next entry's \"> \" or the end of TEXT -- i.e. that command's own
echo and reply, verbatim, exactly as abella_mcp printed them.

The number of chunks always matches
`abella-mcp--count-transcript-entries', and chunk i always corresponds
to the i-th command actually processed (`send_commands', abella_mcp,
handles commands strictly in order) -- a caller that already knows the
exact source text it sent, positionally, never needs to parse a
chunk's own echoed command text back out of TEXT (and abella_mcp's
echo strips comments before printing it, so it usually wouldn't even
match anyway)."
  (let ((start 0) chunks)
    (while (string-match "^> " text start)
      (let* ((chunk-start (match-end 0))
             (next (if (string-match "^> " text chunk-start)
                       (match-beginning 0)
                     (length text))))
        (push (substring text chunk-start next) chunks)
        (setq start next)))
    (nreverse chunks)))

(defconst abella-mcp--skip-marker "*** USING skip ***"
  "Abella's own wording when a proof completes via the `skip' tactic --
see abella_mcp's bin/abella_mcp.ml, `skip_marker'.")

(defun abella-mcp--closes-proof-p (raw)
  "Non-nil if RAW (one event's accumulated transcript chunk(s)) signals
that the proof it belongs to has just closed. `Proof_state.summarize'
(abella_mcp, bin/proof_state.ml) falls back to Abella's raw, verbatim
reply text whenever there is no proof state left to diff against --
which is exactly the \"Proof completed ...\" case -- so this text
reliably reaches here without any protocol change."
  (string-match-p "Proof completed" raw))

(defun abella-mcp--scan-warnings (event raw)
  "Scan RAW (a newly-added transcript chunk) for known warning-worthy
patterns and push any found onto EVENT's `abella-event-warnings'."
  (when (string-match-p (regexp-quote abella-mcp--skip-marker) raw)
    (push "Proof completed via skip" (abella-event-warnings event))))

(defun abella-mcp--events-from-batch (from positions raw-chunks &optional failed-cmd failed-chunk)
  "Build/update this buffer's session events for one batch.

POSITIONS are the end positions of the commands that succeeded,
starting at FROM (a slice of what `abella-split-commands' returned);
RAW-CHUNKS is the parallel list of their raw transcript chunks (a
slice of what `abella-mcp--split-transcript' returns). If the batch stopped
on an error, FAILED-CMD is that command's own source text and
FAILED-CHUNK its raw chunk.

Updates `abella--pending-theorem' and pushes onto `abella-events' via
the state machine: outside a pending theorem, a Theorem/Split command
opens one (nothing pushed yet); any other command outside a pending
theorem is pushed immediately; inside a pending theorem, a chunk is
folded into it (and checked for closure via
`abella-mcp--closes-proof-p', which finalizes and pushes it). A
failing command always becomes one status=error event, folding in whatever
proof was pending (so a proof that errors out mid-tactic becomes one
failed event for the whole attempt, not two).

Returns the list of newly FINALIZED events, in this batch, in order --
for the caller to append to the display. An event left open in
`abella--pending-theorem' at the end of this batch contributes nothing
to the return value until some later call finalizes it."
  (let ((start from) new-events)
    (cl-loop for end in positions
             for raw in raw-chunks
             do (let ((cmd (buffer-substring-no-properties start end)))
                  (cond
                   (abella--pending-theorem
                    ;; RAW already starts with this command's own echo
                    ;; (everything between one "> " and the next, per
                    ;; `abella-mcp--split-transcript') -- `abella--event-text'
                    ;; only prefixes the very start of the whole
                    ;; accumulated blob with "> ", so every subsequent
                    ;; tactic folded in here needs its own "> " ahead of
                    ;; its already-echo-carrying RAW, or the tactics run
                    ;; together with no cue where one ends and the next
                    ;; begins.
                    (setf (abella-event-raw abella--pending-theorem)
                          (concat (abella-event-raw abella--pending-theorem) "> " raw))
                    (abella-mcp--scan-warnings abella--pending-theorem raw)
                    (when (abella-mcp--closes-proof-p raw)
                      (setf (abella-event-source-marker abella--pending-theorem)
                            (copy-marker end))
                      (push abella--pending-theorem abella-events)
                      (push abella--pending-theorem new-events)
                      (setq abella--pending-theorem nil)))
                   ((member (abella-command-keyword start) '("Theorem" "Split"))
                    (setq abella--pending-theorem
                          (abella-event-create :kind (abella-command-keyword start)
                                                :command cmd :status 'ok :raw raw
                                                :start-marker (copy-marker end)))
                    (abella-mcp--scan-warnings abella--pending-theorem raw))
                   (t
                    (let ((ev (abella-event-create :kind (abella-command-keyword start)
                                                    :command cmd :status 'ok :raw raw
                                                    :source-marker (copy-marker end))))
                      (abella-mcp--scan-warnings ev raw)
                      (push ev abella-events)
                      (push ev new-events))))
                  (setq start end)))
    (when failed-cmd
      (let ((ev (abella-event-create :kind (abella-command-keyword start)
                                      :command failed-cmd :status 'error :raw failed-chunk
                                      :source-marker (copy-marker (abella-locked-position)))))
        (when abella--pending-theorem
          (setf (abella-event-command ev) (abella-event-command abella--pending-theorem))
          (setf (abella-event-kind ev) (abella-event-kind abella--pending-theorem))
          (setf (abella-event-raw ev)
                (concat (abella-event-raw abella--pending-theorem) "> " failed-chunk))
          (setq abella--pending-theorem nil))
        (push ev abella-events)
        (push ev new-events)))
    (nreverse new-events)))

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

(defun abella-mcp--strip-session-tag (text)
  "Extract this buffer's current Abella PROMPT from TEXT (a raw
abella_mcp tool reply) into `abella--prompt', if TEXT ends with a
\"[session: ID | prompt: PROMPT]\" trailer (abella_send/abella_undo's
shape) or \"[session: ID | file: F | cwd: C | prompt: PROMPT]\"
(abella_state's, longer but same tail) -- abella_start attaches one
too. Returns TEXT with that trailer (and the blank line before it)
removed. An error reply carries no such trailer at all (see
`tool_send' in abella_mcp.ml) and is returned unchanged.

Does NOT refresh the output buffer's header line itself -- call
`abella--update-session-tag' separately, in whatever order avoids a
race with anything that erases the output buffer (e.g. after
`abella-show-output', never before -- its own erase would otherwise
wipe the just-inserted header back out)."
  (if (string-match "\n\n\\[session: [^][\n]*\\]\\'" text)
      ;; Capture the outer match's own boundary NOW: the inner
      ;; `string-match' on TAG below overwrites Emacs's single global
      ;; match-data, so re-querying `match-beginning' afterward would
      ;; silently return a position relative to TAG (a much shorter
      ;; string) instead of TEXT -- exactly the bug that first shipped
      ;; here, truncating far more than the trailer.
      (let ((tag (match-string 0 text))
            (cut (match-beginning 0)))
        (when (string-match "prompt: \\([^]|]*\\)\\]\\'" tag)
          (setq abella--prompt (string-trim (match-string 1 tag))))
        ;; abella_mcp builds this as `trim(transcript) ^ "\n\n[session: ...]"'
        ;; (bin/abella_mcp.ml) -- the `trim' already ate the last entry's
        ;; own trailing "\n" (each per-command entry ends with exactly
        ;; one, per `send_commands's own format string) before the tag
        ;; was appended, so cutting the tag back off would otherwise
        ;; leave that last entry with no trailing newline at all, run
        ;; together with whatever follows it.
        (concat (substring text 0 cut) "\n"))
    text))

(defun abella--update-session-tag ()
  "Refresh the single \"[session: ID | prompt: PROMPT]\" header line at
the very top of this buffer's output buffer, in place -- never
repeated the way abella_mcp's own per-reply trailer would be if left
attached to every event (see `abella-mcp--strip-session-tag', which
calls this whenever that trailer changes)."
  ;; Read buffer-local state (`abella--session-tag-marker' and friends)
  ;; here, in the SOURCE buffer's own dynamic extent, not from inside
  ;; `with-current-buffer' on the output buffer below -- see the
  ;; matching comment in `abella--show-live-state'.
  (let* ((buf (get-buffer-create (abella-output-buffer-name)))
         (line (format "[session: %s | prompt: %s]" (or abella-session-id "") abella--prompt))
         (old-end (and abella--session-tag-marker
                       (eq (marker-buffer abella--session-tag-marker) buf)
                       (marker-position abella--session-tag-marker)))
         new-end)
    (with-current-buffer buf
      (unless (derived-mode-p 'abella-output-mode) (abella-output-mode))
      (let ((inhibit-read-only t))
        (goto-char (point-min))
        (when old-end (delete-region (point-min) old-end))
        (insert line "\n\n")
        (setq new-end (point))))
    (unless (and abella--session-tag-marker (eq (marker-buffer abella--session-tag-marker) buf))
      (setq abella--session-tag-marker (make-marker)))
    (set-marker abella--session-tag-marker new-end buf)))

(defvar-local abella--live-state-marker nil
  "Marker in the *abella:...* output buffer at the start of the
currently-displayed live proof state -- a bare-text sub-region at the
very end of the buffer, shown only while a proof is open -- or nil
when there is none. `abella--show-live-state' only ever replaces this
one sub-region, never the persistent event log preceding it (unlike
`abella-show-output', a full erase-and-redraw); `abella--append-events'
clears it before appending a just-finalized event, since that event's
own text (its whole proof's transcript, via `abella-event-raw')
supersedes it.")

(defun abella--show-live-state (text)
  "Show TEXT (a full proof state) as the live-state region at the end
of the output buffer: replaces the previous live-state region if this
buffer's proof is still the one already being shown live, or appends
one fresh (entering a proof, or right after a previous one's region
was cleared)."
  ;; `abella--live-state-marker' is `defvar-local' to the SOURCE buffer
  ;; (like `abella-checkpoints'/`abella-events'), so it must be read and
  ;; written from here, in the source buffer's own dynamic extent --
  ;; not from inside `with-current-buffer' on the output buffer below,
  ;; which would silently read/write that OTHER buffer's own unrelated
  ;; binding of the same buffer-local variable name instead.
  (let* ((buf (get-buffer-create (abella-output-buffer-name)))
         (existing (and abella--live-state-marker
                         (eq (marker-buffer abella--live-state-marker) buf)
                         (marker-position abella--live-state-marker)))
         start)
    (with-current-buffer buf
      (unless (derived-mode-p 'abella-output-mode) (abella-output-mode))
      (let ((inhibit-read-only t))
        (setq start (or existing (point-max)))
        (delete-region start (point-max))
        (goto-char start)
        (unless (or (bobp) (eq (char-before) ?\n)) (insert "\n"))
        (setq start (point))
        (insert text)
        (goto-char start)))
    (unless (and abella--live-state-marker (eq (marker-buffer abella--live-state-marker) buf))
      (setq abella--live-state-marker (make-marker)))
    (set-marker abella--live-state-marker start buf)
    (let ((window (display-buffer buf '(display-buffer-reuse-window
                                         (inhibit-same-window . t)))))
      (when window
        (set-window-point window start)
        ;; `set-window-point' alone only guarantees START is *visible
        ;; somewhere* -- Emacs scrolls minimally to bring it into view,
        ;; which is not the same as showing it at the top. With a
        ;; persistent event log now preceding this region (unlike the
        ;; old design, where the state was the buffer's entire content
        ;; and this distinction didn't exist), the state needs an
        ;; explicit `set-window-start' to actually appear from its own
        ;; first line down, exactly what made this worth doing here in
        ;; the first place (see `abella-show-output's SCROLL-TO-TOP).
        (set-window-start window start t)))))

(defun abella--event-text (event)
  "Render EVENT as display text: its own raw transcript prefixed with
\"> \" (matching the look of the transcript display this replaces),
plus any warnings each on their own indented line, plus a trailing
blank line separating it from whatever comes next."
  (concat "> " (abella-event-raw event)
          (mapconcat (lambda (w) (format "  ! %s\n" w)) (abella-event-warnings event) "")
          "\n"))

(defun abella--append-events (new-events)
  "Append NEW-EVENTS' display text, in order, to this buffer's output
buffer -- without erasing its prior content, unlike `abella-show-output'.
Records each event's `abella-event-output-marker' at its own text's
start, for `abella--truncate-events-to' to use on a later retract.

Auto-scrolls to follow the tail (advances the output buffer's own
point, and any window currently showing it) only for point/windows
that were already at the old end before the insert -- the same \"don't
yank the view back if the user scrolled away\" convention
`compilation-mode'/`comint-mode' use, adapted for a non-process
\(synchronous request/response\) buffer.

First clears any live-state region (see `abella--show-live-state') --
a just-finalized event's own text (its whole proof's transcript, for a
theorem) supersedes it."
  (when new-events
    (let ((buf (get-buffer-create (abella-output-buffer-name)))
          ;; read/cleared here, in the SOURCE buffer's own dynamic
          ;; extent -- see the matching comment in `abella--show-live-state'
          (live-pos (and abella--live-state-marker
                         (marker-buffer abella--live-state-marker)
                         (marker-position abella--live-state-marker))))
      (when abella--live-state-marker
        (set-marker abella--live-state-marker nil)
        (setq abella--live-state-marker nil))
      (with-current-buffer buf
        (unless (derived-mode-p 'abella-output-mode) (abella-output-mode))
        (let ((inhibit-read-only t))
          (when live-pos (delete-region live-pos (point-max))))
        (let* ((inhibit-read-only t)
               (old-end (point-max))
               (point-following (>= (point) old-end))
               (following-windows
                (seq-filter (lambda (w) (>= (window-point w) old-end))
                             (get-buffer-window-list buf nil t))))
          (save-excursion
            (goto-char old-end)
            ;; Separate from whatever's already there -- typically the
            ;; last live proof-state display shown while this event's
            ;; own proof was still open, which isn't itself part of the
            ;; persistent log's own formatting and so isn't guaranteed
            ;; to already end in a newline.
            (unless (or (bobp) (bolp)) (insert "\n"))
            (dolist (ev new-events)
              (setf (abella-event-output-marker ev) (point-marker))
              (insert (abella--event-text ev))))
          (when point-following (goto-char (point-max)))
          (dolist (w following-windows) (set-window-point w (point-max)))))
      (display-buffer buf '(display-buffer-reuse-window (inhibit-same-window . t))))))

(defun abella--truncate-events-to (target)
  "Pop `abella-events' for any finalized event whose own
`abella-event-source-marker' now falls beyond TARGET (mirroring how
`abella-checkpoints' is already popped in the same retract),
truncating the output buffer's displayed text to match via each popped
event's `abella-event-output-marker'. Also discards
`abella--pending-theorem' if TARGET falls before its own
`abella-event-start-marker' -- an event that was never finalized has
nothing to truncate from the display, since it was never appended to
begin with."
  (let (cutoff)
    (while (and abella-events
                (let ((m (abella-event-source-marker (car abella-events))))
                  (and m (marker-buffer m) (> (marker-position m) target))))
      (let ((ev (pop abella-events)))
        (when (abella-event-output-marker ev) (setq cutoff (abella-event-output-marker ev)))
        (set-marker (abella-event-source-marker ev) nil)))
    (when cutoff
      (let ((buf (get-buffer (abella-output-buffer-name))))
        (when (and buf (marker-buffer cutoff))
          (with-current-buffer buf
            (let ((inhibit-read-only t))
              (delete-region (marker-position cutoff) (point-max))))))
      (set-marker cutoff nil))
    (when (and abella--pending-theorem
               (abella-event-start-marker abella--pending-theorem)
               ;; strictly less-than, mirroring how `abella-checkpoints'
               ;; itself is popped via ">" not ">=" -- a target that
               ;; lands exactly on the header's own checkpoint keeps
               ;; that checkpoint (and so this still-open theorem, just
               ;; retracted back to its very start) rather than
               ;; discarding it
               (< target (marker-position (abella-event-start-marker abella--pending-theorem))))
      (set-marker (abella-event-start-marker abella--pending-theorem) nil)
      (setq abella--pending-theorem nil)
      ;; Retracted fully back out of this proof (now at the top level):
      ;; its live-state region, if still showing, is now stale --
      ;; `abella--show-live-state' would otherwise only ever replace it
      ;; on a FUTURE proof state, leaving a discarded proof's last state
      ;; dangling on screen indefinitely.
      ;;
      ;; Capture buffer/position into plain locals BEFORE switching
      ;; buffers below: `abella--live-state-marker' is `defvar-local',
      ;; so re-evaluating that symbol from inside `with-current-buffer'
      ;; on a DIFFERENT buffer would silently read THAT buffer's own
      ;; unrelated binding instead (the same pitfall fixed in
      ;; `abella--show-live-state'/`abella--append-events').
      (when (and abella--live-state-marker (marker-buffer abella--live-state-marker))
        (let ((live-buf (marker-buffer abella--live-state-marker))
              (live-pos (marker-position abella--live-state-marker)))
          (with-current-buffer live-buf
            (let ((inhibit-read-only t))
              (delete-region live-pos (point-max)))))
        (set-marker abella--live-state-marker nil)
        (setq abella--live-state-marker nil)))))

(defun abella-ensure-session ()
  "Return this buffer's session_id, starting it via abella_start if
this is the first use in this Emacs session."
  (unless abella-session-id (setq abella-session-id (abella-session-name)))
  (unless abella-session-started
    (let* ((cwd (and (buffer-file-name) (file-name-directory (buffer-file-name))))
           (args (if cwd `((session_id . ,abella-session-id) (cwd . ,cwd))
                   `((session_id . ,abella-session-id)))))
      (let* ((result (abella-mcp-call-tool "abella_start" args))
             (clean (abella-mcp--strip-session-tag (car result))))
        (setq abella-session-started t)
        (abella-show-output clean)
        (abella--update-session-tag))))
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
state rather than a delta, and with no command transcript attached.
Its own \"[session: ...]\" trailer is stripped out (see
`abella-mcp--strip-session-tag') and used to refresh the output
buffer's header line instead of being left in the state text itself --
this function has no erase-buffer risk of its own to race against, so
the header is refreshed immediately."
  (let* ((raw (car (abella-mcp-call-tool "abella_state" `((session_id . ,abella-session-id)))))
         (clean (abella-mcp--strip-session-tag raw)))
    (abella--update-session-tag)
    (setq abella--last-state clean)))

(defun abella--top-level-state-p (state-text)
  "Non-nil if STATE-TEXT (from abella_state) does NOT represent a real
open proof state. `tool_state' (abella_mcp.ml) falls back to whatever
Abella's session last printed verbatim whenever its own cached
last_state field isn't literally empty -- which includes transient
text like \"Proof completed\" right after a proof closes, not just the
\"(no proof state; at top level)\" sentinel this used to check for
alone (a real bug: it made `abella--report' treat that transient text
as a genuine open state). A real proof state always contains a line of
`=' characters (the hypotheses/goal separator -- see
`Proof_state.parse_state', bin/proof_state.ml in the abella-mcp
project), so that presence is the reliable signal instead."
  (not (string-match-p "^=+[ \t]*$" state-text)))

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
          ;; Strip abella_send's own trailing "[session: ...]" tag (only
          ;; ever present on success -- see `tool_send' in abella_mcp.ml)
          ;; before splitting into per-command chunks, so it never ends
          ;; up embedded in an event's own `abella-event-raw'; no
          ;; erase-buffer risk here (append-only), so the header is
          ;; refreshed right away.
          (setq resp-text (abella-mcp--strip-session-tag resp-text))
          (abella--update-session-tag)
          (let* ((chunks (abella-mcp--split-transcript resp-text))
                 (shown (length chunks))
                 (succeeded (min n (if is-error (max 0 (1- shown)) shown))))
            (dotimes (i succeeded)
              (push (copy-marker (nth i positions)) abella-checkpoints))
            (abella--update-locked-marker)
            ;; Structured events, independent of is-error/is-state below:
            ;; a batch that ends mid-proof (a Theorem just opened, or
            ;; still open from an earlier batch) still finalizes and
            ;; displays whatever OTHER declarations it also processed.
            ;; SHOWN > 0 excludes a purely infrastructure-level failure
            ;; (e.g. the session missing even after `retried') that
            ;; never reached Abella at all -- nothing command-level
            ;; happened there to log.
            (when (or (> succeeded 0) (and is-error (> shown 0)))
              (let* ((failed-cmd
                      (and is-error (> shown 0) (< succeeded n)
                           (buffer-substring-no-properties
                            (if (> succeeded 0) (nth (1- succeeded) positions) from)
                            (nth succeeded positions))))
                     (failed-chunk (and is-error (> shown 0) (nth succeeded chunks))))
                (abella--append-events
                 (abella-mcp--events-from-batch
                  from (seq-take positions succeeded) (seq-take chunks succeeded)
                  failed-cmd failed-chunk))))
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
            (progn (abella--update-locked-marker)
                   (abella--truncate-events-to target)
                   (abella--report text))
          ;; Fast undo failed (e.g. it would cross a completed proof's
          ;; boundary): restart clean and replay up to TARGET instead.
          (dolist (m abella-checkpoints) (set-marker m nil))
          (setq abella-checkpoints nil)
          (dolist (ev abella-events)
            (when (abella-event-source-marker ev) (set-marker (abella-event-source-marker ev) nil)))
          (setq abella-events nil)
          (when abella--pending-theorem
            (when (abella-event-start-marker abella--pending-theorem)
              (set-marker (abella-event-start-marker abella--pending-theorem) nil)))
          (setq abella--pending-theorem nil)
          (when abella--live-state-marker
            (set-marker abella--live-state-marker nil)
            (setq abella--live-state-marker nil))
          ;; `abella-ensure-session' below always re-displays its own
          ;; "Started Abella session" banner via `abella-show-output',
          ;; which erases the output buffer itself -- no need to do it
          ;; again here.
          (setq abella-session-started nil)
          (abella-ensure-session)
          (abella--update-locked-marker)
          (if (<= target (point-min))
              (cons (abella-fetch-state) t)
            (abella-run-region (point-min) target)))))))

(defun abella--display-result (result)
  "Show RESULT, a (TEXT . IS-STATE) pair from `abella-run-region' or
`abella-retract-to', or nil if nothing happened.

IS-STATE non-nil (inside a proof) is shown via `abella--show-live-state'
-- a replaceable sub-region at the end of the buffer, never a full
erase, so it never disturbs the persistent event log preceding it. IS-
STATE nil means the relevant events -- declarations finalized, a
theorem closed, or a failing command -- were already appended to the
output buffer as a side effect of building RESULT (see
`abella-mcp--events-from-batch' and its caller in `abella-run-region'),
so there is nothing further to display for that case; RESULT nil, or
an empty region having been sent, is just `message'd instead of
disturbing the persistent log the way erasing it to show a one-line
notice would."
  (cond
   ((not result) (message "Nothing to undo."))
   ((cdr result) (abella--show-live-state (car result)))
   ((equal (car result) "(nothing to send)") (message "%s" (car result)))))

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
