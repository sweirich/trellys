(require 'comint)
(require 'compile)

(defvar sep-mode-map
   (let ((map (make-sparse-keymap)))
     ;; (define-key map [foo] 'sep-do-foo)
     map)
   "Keymap for `sep-mode'.")

 (defvar sep-mode-syntax-table
   (let ((st (make-syntax-table)))
     (modify-syntax-entry ?- ". 12b" st)
     (modify-syntax-entry ?\n "> b" st)
     st)
   "Syntax table for `sep-mode'.")


(defvar sep-keywords

	'("data" "where"
		"forall" "join"
		"conv" "by" "at"
		"valax" "ord"
		"case" "of"	"tcase"
		"let" "in"
		"ind" "rec"
		"contra" "contraval"
		"Type" "abort"
		"theorem" "type" "prog" "proof" "axiom"
    "module"
	)
)


(defvar sep-builtins
  '(
		;; Ordering
		"ord" "ordtrans"
		;; 'Derived' operators
		"sym" "trans" "refl" "morejoin")
	)

(defvar sep-types
	'("Type" "Nat" "Formula" "LogicalKind" "Bool")
		)

(defvar sep-operators
	'("=>" "->" "=" "<")
	)
(defvar sep-keywords-regexp (regexp-opt sep-keywords 'words))
(defvar sep-types-regexp (regexp-opt sep-types 'words))
(defvar sep-operators-regexp (regexp-opt sep-operators 'words))
(defvar sep-builtins-regexp (regexp-opt sep-builtins 'words))
(defvar sep-variable-regexp "\\b[[:lower:]_][[:alnum:]'_]*\\b")
(defvar sep-constructor-regexp "\\b[[:upper:]][[:alnum:]'_]*\\b")


;; font-lock-builtin-face
;; font-lock-comment-delimiter-face
;; font-lock-comment-face
;; font-lock-constant-face
;; font-lock-doc-face
;; font-lock-function-name-face
;; font-lock-keyword-face
;; font-lock-negation-char-face
;; font-lock-preprocessor-face
;; font-lock-reference-face
;; font-lock-string-face
;; font-lock-type-face
;; font-lock-variable-name-face
;; font-lock-warning-face
(defvar sep-font-lock-keywords
   `(
		 (,sep-keywords-regexp . font-lock-keyword-face)
		 (,sep-types-regexp . font-lock-type-face)
		 (,sep-operators-regexp . font-lock-variable-name-face)
		 (,sep-variable-regexp . font-lock-builtin-face)
		 (,sep-builtins-regexp . font-lock-variable-name-face)
		 (,sep-constructor-regexp . font-lock-type-face)
		 )
   "Keyword highlighting specification for `sep-mode'.")

 ;; (defvar sep-imenu-generic-expression
 ;;   ...)

 ;; (defvar sep-outline-regexp
 ;;   ...)

 ;;;###autoload

 ;;; Indentation

 (defun sep-indent-line ()
   "Indent current line of Sep code."
   (interactive)
   (let ((savep (> (current-column) (current-indentation)))
	 (indent (condition-case nil (max (sep-calculate-indentation) 0)
		   (error 0))))
     (if savep
	 (save-excursion (indent-line-to indent))
       (indent-line-to indent))))

 (defun sep-calculate-indentation ()
   "Return the column to which the current line should be indented."
   0)

(defun sep-comment-dwim (arg)
	"Comment or uncomment current line or region in a smart way.
For details, see `comment-dwim'."
   (interactive "*P")
   (require 'newcomment)
   (let ((deactivate-mark nil) (comment-start "--") (comment-end ""))
     (comment-dwim arg)))


;; Run the typechecker
(defun sep-typecheck-buffer ()
	(interactive)
	(let ((fname (buffer-file-name))
				;; Should pull this from a customizable variable.
				(cmdstr (concat "sep " " --file " buffer-file-name)))
		(set (make-local-variable 'compile-command) cmdstr)
		(call-interactively 'compile)))


(define-derived-mode sep-mode fundamental-mode "Sep"
   "A major mode for editing Sep files."
   :syntax-table sep-mode-syntax-table
   (set (make-local-variable 'comment-start) "-- ")
   ;; (set (make-local-variable 'comment-start-skip) "#+\\s-*")
   (set (make-local-variable 'font-lock-defaults)
				'(sep-font-lock-keywords))
   ;; (set (make-local-variable 'indent-line-function) 'sep-indent-line)
   ;; (set (make-local-variable 'imenu-generic-expression)
	 ;; 			sep-imenu-generic-expression)
   ;; (set (make-local-variable 'outline-regexp) sep-outline-regexp)

	 ; Add the 'typecheck' command
	 (define-key sep-mode-map (kbd "C-c C-t") 'sep-typecheck-buffer)
	 (define-key sep-mode-map (kbd "C-c C-l") 'sep-repl-load)
	 (define-key sep-mode-map (kbd "C-c C-r") 'sep-repl-reload)

	 ; set up the comments
	 (define-key sep-mode-map [remap comment-dwim] 'sep-comment-dwim)
   )


;; Interactive mode

(defvar inferior-sep-buffer nil)
(defcustom sep-repl-command "sep-repl" "Path to trelly REPL")
(defun sep-run-repl (&optional dont-switch-p)
  (if (not (comint-check-proc "*sep*"))
      (save-excursion (let ((cmdlist nil))
												(set-buffer (apply 'make-comint "sep"
																					 sep-repl-command
																					 nil nil))
												(sep-repl-mode))))
  (setq inferior-sep-buffer "*sep*")
  (if (not dont-switch-p)
      (pop-to-buffer "*sep*")))

(defun sep-repl-send-cmd (cmd &optional args)
	(interactive)
	(sep-run-repl)
	(comint-send-string inferior-sep-buffer cmd)
	(comint-send-string inferior-sep-buffer " ")
	(if args
			(comint-send-string inferior-sep-buffer args))
	(comint-send-string inferior-sep-buffer "\n"))


(defun sep-repl-load ()
	"Load the file in the current buffer."
	(interactive)
	(let ((filename (buffer-file-name)))
				(sep-repl-send-cmd ":load" filename)))


(defun sep-repl-reload ()
	"Reload the current module."
	(interactive)
	(sep-repl-send-cmd ":reload" ""))

;; Cribbed from haskell-inf mode
(define-derived-mode sep-repl-mode comint-mode "Sep-Repl"
	"Mode for interacting with sep interactive process"
	(set (make-local-variable 'comint-prompt-regexp)
			 "^sep> ")

	;(add-hook 'comint-output-filter-functions	'sep-repl-spot-prompt nil t)
  (set (make-local-variable 'compilation-error-regexp-alist)
       sep-repl-error-regexp-alist)
  (set (make-local-variable 'compilation-first-column) 0) ;GHCI counts from 0.
	(compilation-shell-minor-mode 1))

(defconst sep-repl-error-regexp-alist
    `(("^\\(.+?\\):\\([0-9]+\\):\\(\\([0-9]+\\):\\)?\\( \\|\n *\\)\\(Warning\\)?"
     1 2 4 ,@(if (fboundp 'compilation-fake-loc)
                 '((6) nil (5 '(face nil font-lock-multiline t)))))))


(provide 'sep-mode)

