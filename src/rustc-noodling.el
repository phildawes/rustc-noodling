

(defun mark-column ()
  (exchange-point-and-mark)
  (let ((col (current-column)))
    (exchange-point-and-mark)
    col))

(defun mark-line ()
  (exchange-point-and-mark)
  (let ((col (line-number-at-pos)))
    (exchange-point-and-mark)
    col))
	

(defun rustc-get-type ()
  "Call into rust-noodling to get some type information"
  (interactive)
  (let ((tmp-file (make-temp-file "rustc-noodling")))
    (write-region nil nil tmp-file nil 'silent)
    (message 
     (--first (or (s-starts-with? "TYPE" it) (s-starts-with? "NO TYPE" it))
	       (apply #'process-lines "/home/pld/src/rust/rustc-noodling/target/release/main" 
		      (list (number-to-string (line-number-at-pos))
			    (number-to-string (current-column))
			    (number-to-string (mark-line))
			    (number-to-string (mark-column))
			    tmp-file
			    (buffer-file-name)))))
    (delete-file tmp-file)))

(global-set-key (kbd "M-p") #'rustc-get-type)


(--filter (s-starts-with? "MATCH" it) (list "MATCH phil" "phil"))


