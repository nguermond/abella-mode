;; Copyright (C) 2026  Nathan Guermond
;; SPDX-License-Identifier: GPL-3.0-or-later
;; Version 0.1.1

;; Inline LaTeX previews for Abella theorem files, via abella_mcp's
;; abella2tex tool and the MELPA `math-preview' package.
;;
;; This file is entirely optional: `abella.el' and `abella-mcp.el' never
;; reference it, so a user who doesn't load it gets abella-mode exactly as
;; it works without this feature. Two independent things can be missing --
;; the `math-preview' Emacs package, and the `abella2tex' opam package on
;; the abella_mcp side (it "must be installed separately", per abella-mcp's
;; own README) -- and both degrade to a plain message from
;; `abella-tex-toggle-preview' rather than breaking anything else.
;;
;; Load this after abella.el and abella-mcp.el; it uses functions from both
;; (abella-command-start and friends from abella.el, abella-mcp-call-tool
;; and abella-output-buffer-name from abella-mcp.el).
;;
;; Rendering always happens in the *abella:...* OUTPUT buffer, never the
;; .thm source buffer: `C-c C-l' toggles a persistent per-(source-)buffer
;; flag, `abella-tex--render-output-p'. While it's on, every future
;; output-buffer display -- a full proof state (every hypothesis, and the
;; goal, each rendered separately since abella2tex renders one term at a
;; time) or a finalized session event (each top-level command --
;; declarations, or a whole theorem once its proof closes -- kept as a
;; persistent, append-only log by abella-mcp.el's own `abella-events',
;; likewise) alike -- shows as TeX instead of plain Abella syntax, for as
;; long as the flag stays on -- this is done via `:after' advice on
;; `abella--show-live-state' and `abella--append-events' (abella-mcp.el),
;; rather than by duplicating every call site that can update the output
;; buffer (stepping, retracting, and even TAB-triggered indentation can
;; all resync and redisplay the state -- advising the two shared display
;; functions catches all of them for free). A finalized event is rendered
;; straight from its own `abella-event-command' (clean source text
;; abella-mcp.el already captured from the source buffer), not by
;; re-parsing whatever ended up displayed -- unlike the earlier version
;; of this file, which had to regex-guess command boundaries out of the
;; output buffer's own text, the same guesswork the ad hoc region-preview
;; case below still needs (`abella-tex--strip-header'), since a manually
;; selected region has no such structured event behind it.
;; Turning the flag off only removes the overlays math-preview placed;
;; since an overlay changes display, not text, the plain state/log
;; underneath is still there and reverts instantly. A selected region
;; gets an ad hoc one-shot render instead, also shown in the output
;; buffer, independent of this persistent mode.

(require 'cl-lib)

(defgroup abella nil
  "Abella proof assistant mode."
  :group 'languages)

(defcustom abella-tex-notation-configs nil
  "List of abella2tex notation config file paths for this project.
Relative paths are resolved against the buffer's `default-directory'
before being sent to abella_mcp -- the shared abella_mcp process's own
cwd is whatever buffer happened to start it first, not necessarily
related to the current buffer's directory, so relative paths must be
expanded on the Emacs side. Typically set per-project via
`.dir-locals.el'.

When nil (the default), a file named `notation.conf' in the same
directory as the current buffer's file is used instead, if one exists
-- see `abella-tex--auto-notation-config'. Setting this variable
disables that auto-discovery; it is used exactly as given."
  :type '(repeat file)
  :group 'abella)

(defvar abella-tex--math-preview-available (require 'math-preview nil t)
  "Non-nil if the `math-preview' package (MELPA) could be loaded.
When nil, `abella-tex-toggle-preview' reports this via `user-error'
instead of failing to load abella-tex.el at all.")

;; ------------------------------------------------------------------
;; Calling abella2tex
;; ------------------------------------------------------------------

(defun abella-tex--auto-notation-config ()
  "Path to a `notation.conf' file in the same directory as the current
buffer's file, if one exists, else nil. Used by `abella-tex--configs-arg'
as a fallback when `abella-tex-notation-configs' is unset."
  (let ((dir (and buffer-file-name (file-name-directory buffer-file-name))))
    (when dir
      (let ((path (expand-file-name "notation.conf" dir)))
        (and (file-exists-p path) path)))))

(defun abella-tex--configs-arg ()
  "The `configs' argument for the abella2tex tool call: an absolute-path
JSON array built from `abella-tex-notation-configs', or, when that is
unset, from `abella-tex--auto-notation-config'."
  (let ((configs (or abella-tex-notation-configs
                      (let ((auto (abella-tex--auto-notation-config)))
                        (and auto (list auto))))))
    (vconcat (mapcar (lambda (p) (expand-file-name p default-directory)) configs))))

;; ------------------------------------------------------------------
;; Buffer-based header stripping for the ad hoc region-selection
;; preview (`abella-tex--preview-region-in-output'), the one remaining
;; case with no `abella-event'/`decl' behind it at all -- just
;; arbitrary selected text, so there is no structured info to read and
;; this still has to parse. Operates on a real (temp) buffer with
;; `abella-mode-syntax-table' active, via `abella-skip-whitespace-and-
;; comments' (abella.el) -- the same primitive `abella-mcp--parse-decl'
;; and friends (abella-mcp.el) now use to build EVERY event's own
;; structured `decl' at creation time, straight off real source-buffer
;; positions; this file no longer re-derives name/type from a detached
;; `abella-event-command' string the way it used to (see
;; `abella-tex--render-define-heading'/`abella-tex--theorem-heading-
;; row', below, which just read `decl' fields directly now).

(defun abella-tex--looking-at-keyword-p (keyword)
  "Non-nil if point is at KEYWORD as a whole word in the current
buffer. On a match, also moves point past KEYWORD and any following
noise (`abella-skip-whitespace-and-comments', abella.el); leaves point
untouched otherwise, so callers can try several keywords in sequence
at the same position via `or'."
  (when (looking-at (concat "\\<" (regexp-quote keyword) "\\>"))
    (goto-char (match-end 0))
    (abella-skip-whitespace-and-comments)
    t))

(defun abella-tex--with-command-buffer (command fn)
  "Call FN with point at the start of a temp buffer containing COMMAND,
`abella-mode-syntax-table' active (so `forward-comment' -- and hence
`abella-skip-whitespace-and-comments'/`abella-tex--looking-at-keyword-p'
-- treats COMMAND's comments exactly as the real source buffer would)
and `case-fold-search' nil (Abella's keywords are case-sensitive, e.g.
`Split' the command vs. `split' the tactic). Returns FN's own value."
  (with-temp-buffer
    (insert command)
    (set-syntax-table abella-mode-syntax-table)
    (let ((case-fold-search nil))
      (goto-char (point-min))
      (funcall fn))))

(defun abella-tex--strip-header (s)
  "Strip a leading Abella top-level header from S, so a statement or
clause list pasted straight from a .thm file parses as a bare
term/clause-list: \"Theorem NAME :\"/\"Lemma NAME :\" up through the
first colon, \"Define ... by\"/\"CoDefine ... by\" up through \"by\", or
a bare \"Query\" keyword. Mirrors the standalone abella2tex CLI's own
`strip_header' (bin/main.ml in the abella2tex project) -- verified by
reading the abella-mcp source that its abella2tex *tool* does NOT do
this itself despite its docstring implying it does (tex_tool.real.ml
calls Pipeline.render directly on the given source with no such step),
so this has to happen here instead."
  (string-trim
   (abella-tex--with-command-buffer
    s
    (lambda ()
      (abella-skip-whitespace-and-comments)
      (cond
       ((or (abella-tex--looking-at-keyword-p "Theorem")
            (abella-tex--looking-at-keyword-p "Lemma"))
        (if (re-search-forward ":" nil t)
            (buffer-substring-no-properties (point) (point-max))
          (buffer-substring-no-properties (point-min) (point-max))))
       ((or (abella-tex--looking-at-keyword-p "Define")
            (abella-tex--looking-at-keyword-p "CoDefine"))
        (if (re-search-forward "\\<by\\>" nil t)
            (buffer-substring-no-properties (point) (point-max))
          (buffer-substring-no-properties (point-min) (point-max))))
       ((abella-tex--looking-at-keyword-p "Query")
        (buffer-substring-no-properties (point) (point-max)))
       (t (buffer-substring-no-properties (point-min) (point-max))))))))

(defun abella-tex--render (source mode configs)
  "Render SOURCE (Abella source syntax) to TeX via abella_mcp's abella2tex
tool, under MODE (\"term\", \"clauses\", or \"commands\"), using CONFIGS
(a vector as built by `abella-tex--configs-arg' -- the caller's job to
compute, in whatever buffer is actually the right one to resolve
`abella-tex-notation-configs'/`notation.conf' against; see the note on
`abella-tex--render-and-show'). Returns \(TEX-STRING . IS-ERROR), same
shape as `abella-mcp-call-tool'. abella2tex is stateless (no
session_id), so no session bookkeeping is needed here.

Always requests \"macros\" (a \\newcommand preamble for every macro the
notation configuration(s) declare -- including abella2tex's own
built-in \\rel/\\ktype/\\abella/\\ind/\\coind, which every rendering uses)
so the returned string is self-contained: MathJax (via math-preview)
has no preamble of its own and errors on an undefined control sequence
otherwise. Verified directly against math-preview's daemon that a
\\newcommand block placed ahead of the math content in the same \"tex\"
payload is processed correctly, so this is simpler and more robust
than trying to register the macros with math-preview itself
(`math-preview-tex-macros' is baked into its daemon process's startup
arguments, not sent per-request, so using it here would mean
restarting that shared daemon on every notation-config change)."
  (let ((source (if (equal mode "commands") source (abella-tex--strip-header source))))
    (abella-mcp-call-tool
     "abella2tex"
     `((source . ,source)
       (mode . ,mode)
       (configs . ,configs)
       (macros . t)
       ;; For "term" mode, this asks abella2tex to wrap a long statement
       ;; across several aligned rows instead of leaving it one
       ;; unbroken line (Render.wrapped_term, abella2tex lib/render.ml
       ;; -- as of abella2tex 0.1.4, "term" mode's own wrapping carries
       ;; no \[ \] delimiter, unlike "commands" mode's unconditional
       ;; wrapping of a lone Kind/Type/Theorem, which still needs
       ;; `abella-tex--unwrap-display' to strip one).
       (display . t)))))

(defun abella-tex--unwrap-display (rendered)
  "Post-process RENDERED (a \\newcommand macros preamble, a blank line,
then the body -- `abella-tex--render' always requests macros) into
\(TEX . WARNING\): TEX is a string ready to hand to math-preview, or nil
if there is nothing to preview; WARNING is abella2tex's own trailing
diagnostic (e.g. an unused configured symbol, or a variable-naming
collision the rendering would introduce -- see the abella2tex tool's
own description), if RENDERED carried one, else nil.

Three things RENDERED can carry that math-preview/MathJax cannot
accept as literal math content:
- A trailing warning line. abella-mcp's abella2tex tool appends any
  diagnostic AFTER the actual rendering (\"OUT ^ warnings\" in
  tex_tool.real.ml); every abella2tex warning, in turn, is printed via
  the one shared `Diag.warn'/`warn_once' (lib/diag.ml in the abella2tex
  project), which always prefixes it \"abella2tex: warning: \" -- a
  fixed, reliable marker for exactly where the real rendering ends and
  the warning begins. Concretely, THIS was why some declarations
  \(e.g. a Define using several notation-config symbols the rest of a
  small snippet doesn't happen to use\) silently failed to render: the
  English-language warning text was being submitted to MathJax right
  along with the real TeX, which cannot parse it.
- A wrapping \\[ ... \\] (\"commands\" mode's unconditional formatting
  for a lone Kind/Type/Theorem, regardless of the \"display\" flag --
  see `abella-tex--render'), which is stripped back off.
- Empty content (abella2tex's \"commands\" mode silently renders
  nothing for a declaration it has no math form for, e.g.
  Import/Specification/Set/Close), reported as a nil TEX so the caller
  can say so instead of submitting a blank/macros-only image.
A no-op for content that has none of these, e.g. \"term\" mode's own
already-bare output, or Define/CoDefine's
\\begin{align*}...\\end{align*}."
  (let* ((wpos (string-match "^abella2tex: warning: " rendered))
         (warning (and wpos (string-trim (substring rendered wpos))))
         (rendered (if wpos (substring rendered 0 wpos) rendered))
         (sep (string-match "\n\n" rendered))
         (macros (if sep (substring rendered 0 sep) ""))
         (body (string-trim (if sep (substring rendered (match-end 0)) rendered))))
    (when (string-match "\\`\\\\\\[\\(\\(?:.\\|\n\\)*\\)\\\\\\]\\'" body)
      (setq body (string-trim (match-string 1 body))))
    (cons (unless (string-empty-p body) (concat macros "\n\n" body)) warning)))

;; ------------------------------------------------------------------
;; math-preview backend
;; ------------------------------------------------------------------

(defun abella-tex--start-math-preview ()
  "Ensure the math-preview daemon is running, or report why it couldn't
be started (e.g. the Node.js CLI isn't installed) without raising."
  (condition-case err
      (progn (math-preview-start-process) t)
    (error (message "abella-tex: could not start math-preview: %s" (error-message-string err)) nil)))

(defun abella-tex--show (beg end tex)
  "Render TEX as an inline image over [BEG, END) in the current buffer
via math-preview."
  (when (abella-tex--start-math-preview)
    (math-preview--submit beg end tex "tex" nil)))

(defun abella-tex--clear (beg end)
  "Remove any math-preview overlay(s) covering [BEG, END) in the current
buffer. Returns non-nil if anything was removed."
  (let ((ovs (math-preview--overlays beg end)))
    (dolist (ov ovs) (delete-overlay ov))
    (and ovs t)))

(defun abella-tex--render-and-show (source mode configs beg end &optional quiet heading)
  "Render SOURCE under MODE (with CONFIGS -- see `abella-tex--render')
via `abella-tex--render' and show it over [BEG, END) in the current
buffer via `abella-tex--show', or `message' why not: a tool error,
nothing to preview, or a warning abella2tex reported alongside an
otherwise-successful rendering (see `abella-tex--unwrap-display') --
unless QUIET, which silently skips all three instead (used when
rendering many hypotheses/goals or transcript entries at once, where
messaging per one would be noisy -- the same notation-config warning,
in particular, tends to repeat near-identically for every declaration
in a file, since each only uses a handful of a whole config's
symbols).

CONFIGS is always passed in by the caller rather than computed here
via `abella-tex--configs-arg', because this function -- like
`abella-tex--render-state-in-buffer' and
`abella-tex--render-events-in-buffer' below it -- typically runs with
`current-buffer' switched to the *abella:...* output buffer (never
visiting a file, so `buffer-file-name' is nil there and
`abella-tex--auto-notation-config' silently finds nothing): the
caller must resolve CONFIGS earlier, while `current-buffer' is still
the Abella source buffer whose directory/`abella-tex-notation-configs'
actually apply.

HEADING, if non-nil, is a bare TeX math-mode fragment (see
`abella-tex--theorem-heading-row') spliced in above SOURCE's own
rendering, both wrapped together in one array as the single image
placed over [BEG, END) -- used by `abella-tex--render-state-in-buffer'
to show the currently open theorem's own \"Theorem NAME:\" heading
above the first hypothesis (or the goal, if there are none) of the
live proof state, since that state has no \"event\" of its own for
`abella-tex--render-event-and-show''s heading handling to attach to
until the proof closes."
  (let ((result (abella-tex--render source mode configs)))
    (if (cdr result)
        (unless quiet (message "abella2tex: %s" (car result)))
      (let* ((unwrapped (abella-tex--unwrap-display (car result)))
             (tex (car unwrapped)) (warning (cdr unwrapped)))
        (when (and warning (not quiet)) (message "%s" warning))
        (if (not tex)
            (unless quiet (message "abella-tex: nothing to preview here."))
          (abella-tex--show
           beg end
           (if heading
               (let ((split (abella-tex--split-macros tex)))
                 (concat (car split) "\n\n\\begin{array}{l}\n"
                         heading " \\\\\n" (cdr split) "\n\\end{array}"))
             tex)))))))

;; ------------------------------------------------------------------
;; Parsing a full proof-state display in the output buffer
;; ------------------------------------------------------------------

(defun abella-tex--hyp-name (line)
  "Elisp port of abella-mcp's bin/proof_state.ml `hyp_name': if LINE
\(assumed not indented\) looks like a hypothesis's opening line
\"NAME : ...\", return (NAME . FORMULA-COLUMN) -- FORMULA-COLUMN is
LINE's 0-based column where the formula text itself starts, right
after \": \" -- else nil."
  (let ((i (cl-position ?: line)))
    (when (and i (> i 0) (< (1+ i) (length line))
               (eq (aref line (1- i)) ?\s) (eq (aref line (1+ i)) ?\s))
      (let ((name (string-trim (substring line 0 (1- i)))))
        (when (and (> (length name) 0) (string-match-p "\\`[A-Za-z0-9_']+\\'" name))
          (cons name (+ i 2)))))))

(defun abella-tex--render-state-in-buffer (beg configs &optional heading)
  "In the current buffer -- assumed to be the *abella:...* output buffer,
just filled with a full proof-state display by `abella--show-live-state'
over [BEG, `point-max') (a sub-region at the tail of the buffer,
following whatever persistent event log precedes it -- never the whole
buffer, unlike the command-transcript case) -- render each hypothesis's
formula and the goal as TeX in place, via `abella-tex--render-and-show',
using CONFIGS (see `abella-tex--render-and-show'; the caller must
resolve this from the Abella source buffer, not this output buffer).
A no-op if [BEG, `point-max') doesn't actually hold a state (no \"====\"
separator line is found -- e.g. \"(no proof state; at top level)\"), so
this is always safe to call on whatever that region currently shows.

HEADING, if non-nil (see `abella-tex--render-and-show'), is spliced in
above the FIRST thing actually rendered -- the first hypothesis, or
the goal if there are none -- so the currently open theorem's own
\"Theorem NAME:\" shows above the live state too, not just once its
proof closes and it becomes a persistent event (the caller must
resolve this from `abella--pending-theorem' in the Abella source
buffer, same reasoning as CONFIGS).

A line-based re-implementation of abella-mcp's own
bin/proof_state.ml parser (`hyp_name', `is_indented', `is_separator'),
operating on the buffer directly (rather than a string, the way
abella-mcp's own Elisp side reads proof states elsewhere) since
overlays need real buffer positions to anchor to."
  (goto-char beg)
  (let (hyps cur-name cur-beg)
    (while (and (not (eobp)) (not (looking-at "=+[ \t]*$")))
      (let* ((bol (line-beginning-position)) (eol (line-end-position))
             (line (buffer-substring-no-properties bol eol))
             (indented (or (string-prefix-p " " line) (string-prefix-p "\t" line)))
             (parsed (unless indented (abella-tex--hyp-name line))))
        (cond
         (parsed
          (when cur-name (push (list cur-name cur-beg bol) hyps))
          (setq cur-name (car parsed) cur-beg (+ bol (cdr parsed))))
         ((and cur-name (not indented))
          ;; a non-indented, non-hypothesis line (a "Subgoal ..:"
          ;; header, "Variables: ...", or a message) ends the block
          (push (list cur-name cur-beg bol) hyps)
          (setq cur-name nil))
         (t nil)))
      (forward-line 1))
    (when cur-name (push (list cur-name cur-beg (point)) hyps))
    (setq hyps (nreverse hyps))
    (when (looking-at "=+[ \t]*$")
      (forward-line 1)
      (let* ((goal-beg (point))
             (goal-end (if (re-search-forward "^[ \t]*Subgoal .+ is:\\|^\\[session: " nil t)
                           (line-beginning-position)
                         (point-max))))
        (goto-char goal-end)
        (skip-chars-backward " \t\n")
        (setq goal-end (point))
        (dolist (h hyps)
          (let ((name (nth 0 h)) (beg (nth 1 h)) (end (nth 2 h)))
            (ignore name)
            (save-excursion
              (goto-char end)
              (skip-chars-backward " \t\n")
              (setq end (point)))
            (when (> end beg)
              (abella-tex--render-and-show
               (buffer-substring-no-properties beg end) "term" configs beg end t heading)
              (setq heading nil))))
        (when (> goal-end goal-beg)
          (abella-tex--render-and-show
           (buffer-substring-no-properties goal-beg goal-end) "term" configs goal-beg goal-end t heading))))))

;; ------------------------------------------------------------------
;; Rendering persistent session events in the output buffer
;; ------------------------------------------------------------------

(defun abella-tex--declaration-mode (kw)
  "The abella2tex MODE to render a top-level command starting with
keyword KW under: \"term\" for Theorem/Query, whose own \"display\"
flag actually suppresses \\[ \\] wrapping (so no post-processing is
needed for these, unlike the below); \"commands\" for everything else
\(Kind, Type, Define, CoDefine, ... -- none of these have a
term/clauses-mode equivalent; Kind/Type in particular are not \"a
term\" at all, grammatically\), whose own header-parsing makes
`abella-tex--strip-header' unnecessary, but whose lone-Kind/Type
wrapping and empty output for non-renderable commands (Import/
Specification/Set/Close, or -- for a failed event -- whatever tactic
or malformed text Abella itself rejected) both need
`abella-tex--unwrap-display' afterward -- see `abella-tex--render-and-show',
which every caller of this function goes through."
  (if (member kw '("Theorem" "Query")) "term" "commands"))

(defun abella-tex--split-macros (tex)
  "TEX is a \\newcommand macros preamble, a blank line, then a body --
the shape every non-nil `abella-tex--unwrap-display' TEX always has
\(see `abella-tex--render''s own \"macros\" request\). Returns
\(MACROS . BODY\), so a caller combining two separate renderings (a
Define/CoDefine's own body plus its synthetic type-header rendering,
in `abella-tex--render-event-and-show') can keep just one copy of
MACROS -- both requests carry an identical copy, since it's derived
from the same notation config either way -- instead of emitting the
whole \\newcommand block twice into one image."
  (let ((sep (string-match "\n\n" tex)))
    (if sep (cons (substring tex 0 sep) (substring tex (match-end 0)))
      (cons "" tex))))

(defun abella-tex--splice-align-heading (body heading-row)
  "BODY is a Define/CoDefine event's own rendered body (macros already
split off via `abella-tex--split-macros') -- always a
\\begin{align*}...\\end{align*} block, abella2tex's own fixed
\"commands\"-mode output shape for these two commands (confirmed
empirically, the same way `abella-tex--render''s own \\[ \\] handling
is). Returns BODY with HEADING-ROW (a bare TeX math-mode fragment, no
leading \"&\" or trailing \"\\\\\") spliced in as a new first row, so it
renders above the clauses inside the very same align* block -- keeping
everything as the one combined image `abella-tex--show' places over
the event's whole span, so toggling rendering off still reverts
instantly to the plain, untouched source text underneath.

Falls back to wrapping HEADING-ROW and BODY together in their own
array instead, if BODY doesn't actually start with \\begin{align*} --
defensive only; shouldn't happen for a real Define/CoDefine."
  (if (string-match "\\`\\\\begin{align\\*}\n" body)
      (concat (substring body 0 (match-end 0))
              "  &" heading-row " \\\\\n"
              (abella-tex--indent-clause-rows (substring body (match-end 0))))
    (concat "\\begin{array}{l}\n" heading-row " \\\\\n" body "\n\\end{array}")))

(defun abella-tex--indent-clause-rows (rows)
  "ROWS is a Define/CoDefine event's own align* clause rows (everything
after the opening \\begin{align*} line, through and including the
closing \\end{align*} line) -- abella2tex's `clauses' (lib/render.ml)
always opens a clause's first line with \"  &\" and any of its own
wrapped continuation lines with \"  &\\quad \". Indenting every such
line one further \\quad, here, makes the clauses read as nested under
the \"Define ... by\" heading `abella-tex--splice-align-heading' has
just spliced in above them as an unindented row of its own, reusing
abella2tex's own wrap-indent convention rather than inventing a new
one. The closing \\end{align*} line has no leading \"  &\" and so is
left untouched."
  (replace-regexp-in-string "^  &" "  &\\\\quad " rows))

(defun abella-tex--header-to-type-command (name type)
  "The bare \"Type NAME TYPE.\" command for one (NAME . TYPE) pair off a
Define/CoDefine event's own `abella-define-decl-names-types' --
Abella's own Type declaration syntax has NO colon (e.g. the source
file's own \"Type lvl  tm -> ord -> prop.\"), so NAME and TYPE (already
split apart by `abella-mcp--parse-define-decl', abella-mcp.el) are
simply space-joined rather than needing any colon bookkeeping here."
  (concat "Type " name " " type "."))

(defun abella-tex--render-define-heading (decl keyword configs)
  "The Define/CoDefine heading row TeX (a bare math-mode fragment, no
macros preamble -- see `abella-tex--split-macros') for DECL (an
`abella-define-decl', or nil) under KEYWORD (\"Define\" or
\"CoDefine\"): \"\\text{Define }TYPE1, TYPE2, ...\\ \\text{by}\", each
\(NAME . TYPE\) pair in DECL's own `names-types' rendered as real math
via its own synthetic \"Type ... .\" command (see
`abella-tex--header-to-type-command') fed through abella2tex's
\"commands\" mode -- the very same renderer already used for real
Kind/Type declarations, so it picks up CONFIGS/`notation.conf'
identically -- and every pair's own rendering joined with \", \" (an
ordinary single-name Define is just the one-pair case of this; a
mutual Define, e.g. \"Define foo : ty1, bar : ty2 by ...\", renders
all of them). nil if DECL is nil, has no pairs, or abella2tex rendered
none of them -- silently, same as every other event rendering (see
`abella-tex--render-events-in-buffer')."
  (when decl
    (let ((rendered
           (delq nil
                 (mapcar
                  (lambda (name-type)
                    (let ((result (abella-tex--render
                                   (abella-tex--header-to-type-command (car name-type) (cdr name-type))
                                   "commands" configs)))
                      (unless (cdr result)
                        (let ((unwrapped (abella-tex--unwrap-display (car result))))
                          (when (car unwrapped) (cdr (abella-tex--split-macros (car unwrapped))))))))
                  (abella-define-decl-names-types decl)))))
      (when rendered
        (concat "\\text{" keyword " }" (mapconcat #'identity rendered ", ") "\\ \\text{by}")))))

(defun abella-tex--theorem-heading-row (decl keyword)
  "The Theorem/Query heading row TeX (a bare math-mode fragment) for
DECL (an `abella-theorem-decl', or nil) under KEYWORD (\"Theorem\" or
\"Query\"): \"\\text{Theorem }\\text{NAME}\\text{:}\" if DECL has a
name, else just \"\\text{KEYWORD:}\" (a Query, or a decl-less event,
has none). No abella2tex call needed, unlike
`abella-tex--render-define-heading' -- the name itself is shown as
plain text, not math, so there's no notation to apply."
  (let ((name (and decl (abella-theorem-decl-name decl))))
    (if name (concat "\\text{" keyword " }\\text{" name "}\\text{:}")
      (concat "\\text{" keyword ":}"))))

(defun abella-tex--pending-theorem-heading ()
  "The heading row TeX (see `abella-tex--theorem-heading-row') for
`abella--pending-theorem' -- the Theorem/Split whose proof is
currently open, if any -- or nil if there is none (at the top level,
or between commands). Meant to be called in the Abella SOURCE buffer
\(where `abella--pending-theorem' is the buffer-local one that
matters\), same as `abella-tex--configs-arg', before switching into
the output buffer to actually render the live state; see
`abella-tex--render-state-in-buffer''s own HEADING parameter."
  (when abella--pending-theorem
    (abella-tex--theorem-heading-row
     (abella-event-decl abella--pending-theorem)
     (abella-event-kind abella--pending-theorem))))

(defconst abella-tex--error-marker-tex "\\color{red}{\\textbf{[error]}}"
  "TeX shown, via `abella-tex--show', in place of a failed event's own
rendering -- see `abella-tex--render-event-and-show'. \"color\" is
already one of `math-preview-tex-default-packages', so this needs no
extra MathJax configuration.")

(defun abella-tex--render-event-and-show (ev configs beg end)
  "Render one event EV -- see `abella-tex--render-events-in-buffer',
which calls this once per event -- and show it over [BEG, END), same
as `abella-tex--render-and-show' would for EV's own
`abella-event-command'/mode, except a Define/CoDefine or Theorem/Query
event also gets its own heading row spliced in above its body, both
still as the ONE combined image `abella-tex--show' places over the
event's whole span (so the underlying plain source text, heading
included, is always what reappears the instant rendering is toggled
off -- nothing here ever touches real buffer text, only overlay
`display' properties, exactly like every other renderer in this file).

An event whose `abella-event-status' is `error' never reaches
abella2tex at all -- its own `command'/`raw' is whatever Abella itself
rejected, not necessarily parseable source -- and instead gets
`abella-tex--error-marker-tex' shown over its whole span, so a failed
command reads as a deliberate inline marker in tex mode rather than
silently falling back to plain, unrendered text (easy to mistake for
\"not yet toggled on\").

For any other event, a tool error or empty rendering is skipped
silently, same as `abella-tex--render-and-show' with QUIET -- the only
mode events are ever rendered in (see `abella-tex--render-events-in-buffer').

For a Theorem/Query event with a `decl', the BODY render itself uses
`abella-theorem-decl-statement' instead of the raw `command' -- already
exactly the header-stripped text `abella-tex--strip-header' would
otherwise re-derive from `command', so this skips that redundant
reparse; falls back to `command' unchanged if `decl' is ever nil."
  (if (eq (abella-event-status ev) 'error)
      (abella-tex--show beg end abella-tex--error-marker-tex)
    (let* ((command (abella-event-command ev))
           (kind (abella-event-kind ev))
           (decl (abella-event-decl ev))
           (mode (abella-tex--declaration-mode kind))
           (source (if (and decl (member kind '("Theorem" "Query")))
                       (abella-theorem-decl-statement decl)
                     command))
           (result (abella-tex--render source mode configs)))
      (unless (cdr result)
        (let ((tex (car (abella-tex--unwrap-display (car result)))))
          (when tex
            (let* ((split (abella-tex--split-macros tex))
                   (macros (car split)) (body (cdr split))
                   (combined
                    (cond
                     ((member kind '("Define" "CoDefine"))
                      (let ((heading (abella-tex--render-define-heading decl kind configs)))
                        (if heading (abella-tex--splice-align-heading body heading) body)))
                     ((member kind '("Theorem" "Query"))
                      (concat "\\begin{array}{l}\n"
                              (abella-tex--theorem-heading-row decl kind) " \\\\\n"
                              body "\n\\end{array}"))
                     ((member kind '("Kind" "Type"))
                      ;; Unlike Define/CoDefine, a Kind/Type declaration's
                      ;; own BODY -- via abella2tex's "commands" mode -- is
                      ;; already the complete bare rendering (e.g.
                      ;; "\rel{lvl} : \rel{tm} \to \rel{ord} \to \rel{prop}"
                      ;; for "Type lvl  tm -> ord -> prop."), with no
                      ;; separate clause list below it the way a Define
                      ;; has -- so the keyword is just prefixed directly,
                      ;; no splicing/wrapping/second abella2tex call needed.
                      (concat "\\text{" kind " }" body))
                     (t body))))
              (abella-tex--show beg end (concat macros "\n\n" combined)))))))))

(defun abella-tex--render-events-in-buffer (events configs)
  "In the current buffer -- assumed to be the *abella:...* output
buffer, into which EVENTS (abella-mcp.el's `abella-event' structs, in
order) were just appended by `abella--append-events' -- render each
event's own `abella-event-command' (its clean source text, straight
from the source buffer, not abella_mcp's comment-stripped echo) as TeX
in place, via `abella-tex--render-event-and-show' (using CONFIGS --
see `abella-tex--render-and-show'; the caller must resolve this from
the Abella source buffer, not this output buffer), over just its own
\"> \" + `abella-event-raw' span, MINUS `abella-event-raw's own
trailing newline: from its own `abella-event-output-marker' to one
character short of `abella-event-raw's own length past it -- NOT all
the way to the next event (or `point-max'), which would swallow the
blank-line separator `abella--event-text' (abella-mcp.el) puts after
every event, and any warning lines it carries, into the image's own
replaced region: the separator would disappear entirely (two rendered
commands running together with no break), and warnings -- important,
meant to stay legible -- would be hidden inside an image instead of
left as plain text below it.

The one-character trim matters for the very same reason: a `display'
overlay swallows any newline it spans instead of still breaking the
line there (verified directly -- an overlay covering \"AB\\n\" with a
one-line `display' value renders glued to whatever follows on the SAME
screen line, one fewer screen line overall than the buffer's raw text
would suggest). `send_commands' (abella_mcp's bin/abella_mcp.ml) builds
every transcript entry via \"> %s\\n%s\\n\", so `abella-event-raw'
always ends in exactly one \"\\n\" of its own; covering it here would
eat the only newline standing between this image and whatever
`abella--event-text' put right after it (a warning line, or -- with no
warnings -- the first half of its own trailing blank-line separator),
collapsing what should be a full blank-line gap between two
consecutively-rendered events down to a single, cramped line break.
Excluding it leaves that newline, and `abella--event-text's own outer
one, both real and uncovered, restoring the same blank-line gap plain
(non-tex) mode already has.

For a Theorem/Split event, COMMAND is only its statement -- the image
still replaces the display of its *whole* raw span, tactics and all
(a tactic-by-tactic play-by-play isn't something abella2tex can render
anyway), just not the separator/warnings after it; the underlying text
is untouched regardless, so it's still there, unrendered, the moment
this preview is toggled off. A failed event is rendered the same
uniform way, span-wise, but see `abella-tex--render-event-and-show''s
own `abella-event-status' branch for what actually gets shown there."
  (dolist (ev events)
    (let* ((beg (marker-position (abella-event-output-marker ev)))
           ;; "> " + raw, minus raw's own trailing "\n" -- see above.
           (end (+ beg 2 (1- (length (abella-event-raw ev))))))
      (abella-tex--render-event-and-show ev configs beg end))))

;; ------------------------------------------------------------------
;; Toggle command
;; ------------------------------------------------------------------

(defvar-local abella-tex--render-output-p nil
  "Non-nil while `abella-tex-toggle-preview' has this buffer's Abella
session set to show every future output-buffer display -- a full proof
state (every hypothesis and the goal) or a command transcript (each
top-level command echoed there) alike -- rendered as TeX in its
*abella:...* output buffer, rather than as plain Abella syntax.")

(defun abella-tex--after-show-live-state (text)
  "`:after' advice on `abella--show-live-state' (abella-mcp.el): if
this buffer's `abella-tex--render-output-p' is on, render TEXT (the
full proof state just shown, live, while a proof is open) as TeX over
the live-state region it now occupies -- from this buffer's own
`abella--live-state-marker' to the output buffer's end, the whole of
which TEXT alone now fills (`abella--show-live-state' always clears any
previous live-state region first). Runs with `current-buffer' back to
this Abella source buffer, exactly like the advice this replaces (see
`abella-tex--after-append-events')."
  (ignore text)
  (when (and abella-tex--render-output-p
             abella--live-state-marker (marker-buffer abella--live-state-marker))
    ;; Resolved here, in the SOURCE buffer -- see
    ;; `abella-tex--render-and-show''s note on CONFIGS -- before
    ;; `with-current-buffer' switches into the output buffer below,
    ;; where `abella-tex--configs-arg' couldn't find `notation.conf',
    ;; and `abella--pending-theorem' would be this OTHER buffer's own
    ;; (nil) binding, not the source buffer's.
    (let ((marker abella--live-state-marker) (configs (abella-tex--configs-arg))
          (heading (abella-tex--pending-theorem-heading)))
      (with-current-buffer (marker-buffer marker)
        (abella-tex--render-state-in-buffer (marker-position marker) configs heading)))))

(advice-add 'abella--show-live-state :after #'abella-tex--after-show-live-state)

(defun abella-tex--after-append-events (new-events)
  "`:after' advice on `abella--append-events' (abella-mcp.el): if this
buffer's `abella-tex--render-output-p' is on, render each of NEW-EVENTS
as TeX in place, over its own now-displayed span, via
`abella-tex--render-events-in-buffer'. Runs with `current-buffer' back
to this Abella source buffer (`abella--append-events's own
`with-current-buffer' into the output buffer has already unwound by
the time `:after' advice runs), so `abella-tex--render-output-p' is
read from the right place without needing to pass it explicitly."
  (when (and abella-tex--render-output-p new-events)
    ;; Resolved here, in the SOURCE buffer -- see
    ;; `abella-tex--render-and-show''s note on CONFIGS -- before
    ;; `with-current-buffer' switches into the output buffer below.
    (let ((configs (abella-tex--configs-arg)))
      (with-current-buffer (abella-output-buffer-name)
        (abella-tex--render-events-in-buffer new-events configs)))))

(advice-add 'abella--append-events :after #'abella-tex--after-append-events)

(defun abella-tex--preview-region-in-output (beg end)
  "Render the region [BEG, END) as a bare term and show it in the
output buffer, replacing whatever it currently shows. An ad hoc,
one-shot preview -- not tied to `abella-tex--render-output-p', and not
reverted by a later `abella-tex-toggle-preview' call the way the
persistent state rendering is, since the output buffer's content is
already routinely replaced by ordinary Abella activity."
  (let* ((source (buffer-substring-no-properties beg end))
         (result (abella-tex--render source "term" (abella-tex--configs-arg))))
    (with-current-buffer (get-buffer-create (abella-output-buffer-name))
      (unless (derived-mode-p 'abella-output-mode) (abella-output-mode))
      (let ((inhibit-read-only t))
        (erase-buffer)
        (cond
         ((cdr result) (insert (format "abella2tex error: %s" (car result))))
         (t (let* ((unwrapped (abella-tex--unwrap-display (car result)))
                    (tex (car unwrapped)) (warning (cdr unwrapped)))
              (cond
               (tex (insert "  ") (abella-tex--show (point-min) (point-max) tex))
               (t (insert "(nothing to preview)")))
              (when warning (insert "\n\n" warning)))))
        (goto-char (point-min))))
    (display-buffer (abella-output-buffer-name)
                     '(display-buffer-reuse-window (inhibit-same-window . t)))))

(defun abella-tex-toggle-preview ()
  "With an active region, render exactly the selected text as a bare
term and show it in the *abella:...* output buffer (a one-shot
preview, replacing whatever the output buffer currently shows).

Otherwise, toggle whether this buffer's Abella session shows every
future output-buffer display -- a full proof state or a command
transcript alike, in the output buffer, never this source buffer --
rendered as TeX (goal and every hypothesis, separately, for a state;
each top-level command, for a transcript) instead of as plain Abella
syntax. Turning it back off only removes the images; the plain text
underneath was never touched, so it reappears immediately."
  (interactive)
  (unless abella-tex--math-preview-available
    (user-error "math-preview is not installed (MELPA); install it to enable LaTeX previews"))
  (if (use-region-p)
      (abella-tex--preview-region-in-output (region-beginning) (region-end))
    (setq abella-tex--render-output-p (not abella-tex--render-output-p))
    (if abella-tex--render-output-p
        ;; Resolved once here, in the SOURCE buffer -- see
        ;; `abella-tex--render-and-show''s note on CONFIGS -- before
        ;; either `with-current-buffer' below switches into the output
        ;; buffer.
        (let ((configs (abella-tex--configs-arg)))
          ;; Render whatever the output buffer already shows, the same
          ;; way `abella-tex--after-show-live-state'/
          ;; `abella-tex--after-append-events' render it going forward:
          ;; the live-state region, if a proof is currently open --
          (when (and abella--live-state-marker (marker-buffer abella--live-state-marker))
            (let ((marker abella--live-state-marker)
                  (heading (abella-tex--pending-theorem-heading)))
              (with-current-buffer (marker-buffer marker)
                (abella-tex--render-state-in-buffer (marker-position marker) configs heading))))
          ;; -- and every already-finalized event, oldest first (matching
          ;; buffer/display order; `abella-events' itself is newest first).
          ;; `events' is resolved HERE, still in the source buffer, not
          ;; as part of the `with-current-buffer' call below -- Elisp
          ;; evaluates a `with-current-buffer' body's forms (including
          ;; their own argument subexpressions) only after the buffer
          ;; switch, so `(reverse abella-events)' inlined into that call
          ;; would read the OUTPUT buffer's own (nil) binding instead.
          (let ((events (reverse abella-events)))
            (when events
              (with-current-buffer (abella-output-buffer-name)
                (abella-tex--render-events-in-buffer events configs))))
          (message "abella-tex: output rendering on"))
      (when (get-buffer (abella-output-buffer-name))
        (with-current-buffer (abella-output-buffer-name)
          (abella-tex--clear (point-min) (point-max))))
      (message "abella-tex: output rendering off"))))

(define-key abella-mode-keymap (kbd "C-c C-l") #'abella-tex-toggle-preview)

(provide 'abella-tex)
