((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'coq-prog-args)
			(setq coq-prog-args `("-emacs" "-R" ,(expand-file-name "../src") "Bedrock" "-I" ,(expand-file-name "../src/reification") "-R" ,(expand-file-name "facade") "Facade" "-R" ,(expand-file-name "cito") "Cito")))))))
