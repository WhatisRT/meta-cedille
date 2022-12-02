(setq mc-highlights
      '(("--.*$" . font-lock-comment-face)
        ("let \\|import \\|seteval \\|normalize \\|data \\|where \\|:=\\|\\.\\|:" . font-lock-keyword-face)
        ("?\\|θ\\|γ" . font-lock-function-name-face)
        ("λ\\|Λ\\|Π\\|∀\\|ι\\|->" . font-lock-preprocessor-face)
        ("*\\|□" . font-lock-constant-face)))

(define-derived-mode meta-cedille-mode prog-mode "meta-cedille"
  "Simple major mode for meta-cedille"
  (setq font-lock-defaults '(mc-highlights))
  (setq comment-use-syntax nil)
  (setq comment-start "--"))

(add-hook 'meta-cedille-mode-hook (lambda () (rainbow-delimiters-mode 1)))
(add-hook 'meta-cedille-mode-hook (lambda () (smartparens-mode 1)))

;; (add-to-list 'spacemacs-indent-sensitive-modes 'meta-cedille-mode)
(add-to-list 'sp-no-reindent-after-kill-modes 'meta-cedille-mode)
(add-to-list 'auto-mode-alist '("\\.mced$" . meta-cedille-mode))

;; Repl setup
(defvar meta-cedille-command "meta-cedille" "The name of the meta-cedille executable.")
(defvar meta-cedille-command-args '() "Arguments passed to the executable.") ;; TODO
(defvar meta-cedille-directory nil "The initial working directory.")

(defun meta-cedille-conv-region (start end)
  (replace-regexp-in-string "\n" "" (buffer-substring-no-properties start end)))

(defun meta-cedille-start-process ()
  "Start the REPL"
  (interactive)
  (let ((default-directory meta-cedille-directory))
    (setq meta-cedille-process (make-comint "meta-cedille-repl" meta-cedille-command))
    (if (not (get-buffer-window "*meta-cedille-repl*"))
        (switch-to-buffer-other-window "*meta-cedille-repl*"))))

(defun meta-cedille-send-string (s)
  "Send a string to the repl"
  (interactive "M")
  (comint-send-string meta-cedille-process (concat s "\n")))

(defun meta-cedille-send-region (start end)
  (interactive "r")
  (meta-cedille-send-string (meta-cedille-conv-region start end)))

(defun meta-cedille-send-paragraph ()
  (interactive)
  (save-excursion
    (forward-paragraph)
    (let ((end (point)))
      (backward-paragraph)
      (meta-cedille-send-region (point) end))))

(defun meta-cedille-send-command (cmd s)
  (meta-cedille-send-string (concat cmd " " s ".")))

(defun meta-cedille-load-file ()
  (interactive)
  (save-buffer)
  (meta-cedille-send-command
   "import" (file-relative-name (file-name-sans-extension buffer-file-name) meta-cedille-directory)))

(defun meta-cedille-show-type (s)
  (interactive "M")
  (meta-cedille-send-command "showType" s))

(defun meta-cedille-show-type-dwim ()
  (interactive)
  (if (use-region-p)
      (meta-cedille-show-type (meta-cedille-conv-region (region-beginning) (region-end)))
    (meta-cedille-show-type (symbol-name (symbol-at-point)))))

(defun meta-cedille-restart-process ()
  (interactive)
  (meta-cedille-send-string "")
  (meta-cedille-start-process))

(define-key meta-cedille-mode-map (kbd "C-c C-a") 'meta-cedille-send-paragraph)
(define-key meta-cedille-mode-map (kbd "C-c C-d") 'meta-cedille-show-type-dwim)
(define-key meta-cedille-mode-map (kbd "C-c C-l") 'meta-cedille-load-file)
(define-key meta-cedille-mode-map (kbd "C-c C-p") 'meta-cedille-start-process)
(define-key meta-cedille-mode-map (kbd "C-c C-q") 'meta-cedille-restart-process)
(define-key meta-cedille-mode-map (kbd "C-c C-r") 'meta-cedille-send-region)
(define-key meta-cedille-mode-map (kbd "C-c C-s") 'meta-cedille-send-string)

(provide 'meta-cedille-mode)
