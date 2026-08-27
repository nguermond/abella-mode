;; Copyright (C) 2026  Nathan Guermond
;; SPDX-License-Identifier: GPL-3.0-or-later
;; Version 0.1.0

;; Emacs mode for Abella theorem files.
;;
;; Based on tutorial at:
;;   http://two-wugs.net/emacs/mode-tutorial.html
;;

(defvar abella-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.thm\\'" . abella-mode))

(defun make-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)\\>"))

(defun make-command-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)[^.]*."))

;; Symbolic operators (:=, ->, ;, ...) are made of punctuation-class
;; characters per `abella-mode-syntax-table', so \< and \> never match
;; around them -- they require a word-syntax character on one side.
(defun make-symbol-regex (&rest args)
  (concat "\\(" (regexp-opt args) "\\)"))

(require 'font-lock)
(defvar abella-font-lock-keywords
  (list
    (list (make-command-regex "Set" "Query") 1 font-lock-type-face)
    (cons (make-regex "Import" "Specification") font-lock-preprocessor-face)
    (list (make-command-regex "Type" "Kind" "Close") 1 font-lock-keyword-face)
    (cons (make-regex "Define" "CoDefine" "Theorem" "Split") font-lock-keyword-face)
    (cons (make-regex "skip") font-lock-warning-face)
    (cons (make-regex "by" "type") font-lock-keyword-face)
    (cons (make-regex "forall" "exists" "nabla") font-lock-keyword-face)
    (cons (make-regex "true" "false") font-lock-constant-face)
    (cons (make-regex "intros" "case" "assert" "unfold" "search"
                       "induction" "on" "apply" "to" "with" "backchain" "witness"
                       "left" "right" "split" "as")
          font-lock-builtin-face)
    (cons (make-symbol-regex "/\\" "\\/" "->" ":=" ";")
          font-lock-type-face)
    ;; Hypothesis/case labels (H1, H2, ..., IH, IH1, ...); listed before
    ;; the general variable rule below so it isn't shadowed by it.
    (cons "\\<\\(H[0-9]+\\|IH[0-9]*\\)\\>" font-lock-doc-face)
    ;; Logic variables: Abella's own grammar treats any identifier
    ;; starting with an uppercase letter or underscore as a variable
    ;; (lowercase-initial identifiers are constants/predicates), so
    ;; this isn't a heuristic -- it matches exactly what the parser
    ;; treats as a variable.
    (cons "\\<[A-Z_][A-Za-z0-9_']*\\>" font-lock-variable-name-face))
  "Default highlighting for Abella major mode")

(setq xemacsp (and (boundp 'xemacsp) xemacsp))

(defvar abella-mode-syntax-table
  (let ((abella-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?_ "w"     abella-mode-syntax-table)
    (modify-syntax-entry ?' "w"     abella-mode-syntax-table)
    (modify-syntax-entry ?/ (if xemacsp "w 14" "w 14n") abella-mode-syntax-table)
    (modify-syntax-entry ?* (if xemacsp ". 23" ". 23n") abella-mode-syntax-table)
    (modify-syntax-entry ?% "< b"   abella-mode-syntax-table)
    (modify-syntax-entry ?\n "> b"  abella-mode-syntax-table)
    (modify-syntax-entry ?. "."     abella-mode-syntax-table)
    (modify-syntax-entry ?+ "."     abella-mode-syntax-table)
    (modify-syntax-entry ?- "."     abella-mode-syntax-table)
    (modify-syntax-entry ?= "."     abella-mode-syntax-table)
    (modify-syntax-entry ?> "."     abella-mode-syntax-table)
    (modify-syntax-entry ?< "."     abella-mode-syntax-table)
    (modify-syntax-entry ?# "."     abella-mode-syntax-table)
    (modify-syntax-entry ?\ "."     abella-mode-syntax-table)
    abella-mode-syntax-table)
  "Syntax table for Abella major mode")

;; Proof navigation.  Commands that actually drive an Abella process
;; (rather than just moving point) are bound in modes/abella-mcp.el.
(defvar abella-mode-keymap
  (let ((abella-mode-keymap (make-keymap)))
    abella-mode-keymap)
  "Keymap for Abella major mode")

(defun abella-forward-command ()
  (interactive)
  (search-forward-regexp "%\\|\\.")
  (if (equal (match-string 0) "%")
      (progn (beginning-of-line)
             (next-line 1)
             (abella-forward-command))))


(defun abella-backward-command ()
  (interactive)
  (backward-char 1)
  (abella-backward-command-rec)
  (if (not (bobp))
    (forward-char 1)))

(defun abella-backward-command-rec ()
  (interactive)
  (while (search-backward "%" (point-at-bol) t))
  (if (not (search-backward "." (point-at-bol) t))
      (progn
        (beginning-of-line 1)
        (if (not (bobp))
            (progn (end-of-line 0)
                   (abella-backward-command-rec))))))

;; Indentation.
;;
;; Rules:
;; - a fresh clause head within a `Define'/`CoDefine' block is indented
;;   2 spaces relative to the enclosing `Define';
;; - continuing a clause across multiple lines adds 2 more spaces;
;; - each enclosing pair of parentheses adds 2 more spaces.
;;
;; A "command" is the text between two top-level (depth 0, outside
;; comments/strings) periods; `Define'/`CoDefine' commands consist of a
;; header ending in `by' followed by `;'-separated clauses.

(defun abella-top-level-p (pos)
  "Non-nil if POS is outside any parentheses, comment, or string."
  ;; `syntax-ppss' leaves point at POS instead of restoring it, which
  ;; would derail callers that drive a search loop off (point).
  (let ((state (save-excursion (syntax-ppss pos))))
    (and (= (nth 0 state) 0) (not (nth 3 state)) (not (nth 4 state)))))

(defun abella-find-top-level (regexp from to)
  "Return the position after the last top-level match of REGEXP in
[FROM, TO), or nil if there is none."
  (when (< from to)
    (save-excursion
      (goto-char from)
      (let (result)
        (while (re-search-forward regexp to t)
          (when (abella-top-level-p (match-beginning 0))
            (setq result (point))))
        result))))

(defconst abella-top-level-keyword-regexp
  "\\<\\(Kind\\|Type\\|Close\\|Define\\|CoDefine\\|Theorem\\|Query\\|Set\\|Import\\|Specification\\|Split\\)\\>"
  "Matches the keyword that starts a top-level Abella command.")

(defun abella-find-first-top-level (regexp from to)
  "Return the position of the start of the first top-level match of
REGEXP in [FROM, TO), or nil if there is none."
  (when (< from to)
    (save-excursion
      (goto-char from)
      (let (result)
        (while (and (not result) (re-search-forward regexp to t))
          (when (abella-top-level-p (match-beginning 0))
            (setq result (match-beginning 0))))
        result))))

(defun abella-find-last-top-level-start (regexp from to)
  "Return the start position of the last top-level match of REGEXP in
[FROM, TO), or nil if there is none."
  (when (< from to)
    (save-excursion
      (goto-char from)
      (let (result)
        (while (re-search-forward regexp to t)
          (when (abella-top-level-p (match-beginning 0))
            (setq result (match-beginning 0))))
        result))))

(defun abella-command-start (pos)
  "Return the position where the Abella command containing POS begins."
  (save-excursion
    (goto-char (point-min))
    (let ((start (point-min)))
      (while (re-search-forward "\\." pos t)
        (when (abella-top-level-p (match-beginning 0))
          (setq start (point))))
      start)))

(defun abella-command-keyword (cmd-start)
  "Return the leading keyword of the command starting at CMD-START."
  (save-excursion
    (goto-char cmd-start)
    (while (or (> (skip-chars-forward " \t\n") 0)
               (forward-comment 1)))
    (when (looking-at "[A-Za-z]+")
      (match-string-no-properties 0))))

(defun abella-blank-region-p (from to)
  "Non-nil if the region [FROM, TO) is only whitespace and comments."
  (save-excursion
    (save-restriction
      (narrow-to-region from to)
      (goto-char from)
      (while (or (> (skip-chars-forward " \t\n") 0)
                 (forward-comment 1)))
      (eobp))))

(defun abella-header-indent-column (cmd-start)
  "Return the column at which continuation lines of a Define/CoDefine
header should align: the column of the first predicate name, if it
appears on the same line as the keyword; otherwise a flat 2-space indent."
  (save-excursion
    (goto-char cmd-start)
    (while (or (> (skip-chars-forward " \t\n") 0)
               (forward-comment 1)))
    (skip-chars-forward "A-Za-z")
    (skip-chars-forward " \t")
    (if (eolp) 2 (current-column))))

(defun abella-quantifier-depth (from to)
  "Count lines in [FROM, TO) that begin with a quantifier (forall/exists/
nabla) and whose scope is still open at TO -- i.e. we have not yet closed
past the paren depth they were introduced at.  Each such line adds 2
spaces of indentation to everything within its scope, and unlike parens,
a quantifier's scope is never explicitly closed except by leaving the
parenthesized context (or clause) it was introduced in."
  (let ((depth-at-to (car (save-excursion (syntax-ppss to))))
        (to-line-start (save-excursion (goto-char to) (beginning-of-line) (point)))
        (count 0))
    (save-excursion
      (goto-char from)
      (beginning-of-line)
      (when (< (point) from) (forward-line 1))
      ;; Stop before the line containing TO -- that is the line we are
      ;; indenting, never a previous line contributing to its own indent.
      (while (< (point) to-line-start)
        (let ((line-start (point)))
          (skip-chars-forward " \t")
          (when (and (looking-at "\\(forall\\|exists\\|nabla\\)\\>")
                     (<= (car (save-excursion (syntax-ppss line-start)))
                         depth-at-to))
            (setq count (1+ count)))
          (goto-char line-start))
        (forward-line 1)))
    count))

(defvar-local abella-subgoal-depth-function nil
  "If non-nil, a function of one argument POS returning the live
session's current subgoal nesting depth at POS (1 for a lone/first
pending subgoal, one more per dot in \"Subgoal N.N.N\"), or nil if
that is not available or does not apply at POS -- no session running,
POS is behind where it has processed, etc. Set by modes/abella-mcp.el
when loaded; indentation inside a proof falls back to 0 when this is
nil or returns nil, per that function's own contract.")

(defun abella-in-theorem-proof-p (pos)
  "Non-nil if POS lies in a Theorem/Split's tactic script, i.e. after
its statement's terminating period rather than still within the
statement itself."
  (let ((kw-start (abella-find-last-top-level-start
                    abella-top-level-keyword-regexp (point-min) pos)))
    (and kw-start
         (member (abella-command-keyword kw-start) '("Theorem" "Split"))
         (> (abella-command-start pos) kw-start))))

(defun abella-calculate-indentation ()
  "Compute the indentation column for the current line."
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t")
    (let* ((pos (point))
           (depth (car (syntax-ppss pos)))
           (cmd-start (abella-command-start pos))
           (keyword (abella-command-keyword cmd-start))
           (base
            (cond
             ;; Inside a Theorem/Split's tactic script: every tactic is
             ;; its own period-terminated "command", so the blank-region
             ;; check below would otherwise fire for nearly every line
             ;; here and short-circuit to 0 before this is ever reached.
             ((abella-in-theorem-proof-p pos)
              (let ((subgoal-depth
                     (and abella-subgoal-depth-function
                          (funcall abella-subgoal-depth-function pos))))
                (if subgoal-depth (* 2 (1- subgoal-depth)) 0)))
             ;; Nothing but whitespace/comments before this line within the
             ;; command: this line starts the command itself.
             ((abella-blank-region-p cmd-start pos) 0)
             ((and keyword (member keyword '("Define" "CoDefine")))
              (let ((by-end (abella-find-top-level "\\<by\\>" cmd-start pos)))
                (if (not by-end)
                    (if (looking-at "\\<by\\>")
                        0 ;; `by' on its own line goes back to column 0
                      ;; still within the header, before `by': align a
                      ;; mutual declaration's later predicate names with
                      ;; the first
                      (abella-header-indent-column cmd-start))
                  (let ((clause-start
                         (or (abella-find-top-level ";" by-end pos) by-end)))
                    (if (not (abella-blank-region-p clause-start pos))
                        ;; continuing an existing clause: +2 more for
                        ;; each quantifier scope still open at this line
                        (+ 4 (* 2 (abella-quantifier-depth clause-start pos)))
                      2))))) ;; fresh clause head
             (t 0))))
      (+ base (* 2 depth)))))

(defun abella-indent-line ()
  "Indent the current line according to Abella's block/clause/paren structure."
  (interactive)
  (let ((savep (> (current-column) (current-indentation)))
        (indent (max (abella-calculate-indentation) 0)))
    (if savep
        (save-excursion (indent-line-to indent))
      (indent-line-to indent))))

(defun abella-mode ()
  "Major mode for editing abella theorem files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table abella-mode-syntax-table)
  (use-local-map abella-mode-keymap)
  (set (make-local-variable 'font-lock-defaults)
       '(abella-font-lock-keywords))
  (setq comment-start "%")
  ;; Abella's syntax is genuinely case-sensitive (e.g. the `Split'
  ;; command vs. the `split' tactic); case-fold-search defaults to t,
  ;; which would make our keyword-boundary scanning above mistake one
  ;; for the other.
  (setq case-fold-search nil)
  (setq-local indent-line-function #'abella-indent-line)

  (setq major-mode 'abella-mode)
  (setq mode-name "Abella")
  (run-mode-hooks 'abella-mode-hook))

(provide 'abella-mode)
