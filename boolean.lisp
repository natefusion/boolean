(defun xor (x y)
  (or (and (not x) y) (and x (not y))))

(defun split-bit (num size)
  (loop for x from (1- size) downto 0
        collect (logbitp x num)))

(defun bool->bit (x)
  (if x 1 0))

(defun the-same (f1 f2)
  (let ((num-of-variables-f1 (length (sb-introspect:function-lambda-list f1)))
        (num-of-variables-f2 (length (sb-introspect:function-lambda-list f2))))
    
    (when (/= num-of-variables-f1 num-of-variables-f2)
      (return-from the-same nil))

    (dotimes (x (expt 2 num-of-variables-f1) t)
      (unless (eq (apply f1 (split-bit x num-of-variables-f1))
                  (apply f2 (split-bit x num-of-variables-f1)))
        (return-from the-same nil)))))

(defun truth-table (function)
  (let* ((lambda-list (sb-introspect:function-lambda-list function))
         (num-of-variables (length lambda-list))
         (num-of-rows (expt 2 num-of-variables)))
    
    (format t "~{~A ~}~%"  lambda-list)

    (dotimes (x num-of-rows)
      (format t "~{~A~} | ~a~%" (mapcar #'bool->bit (split-bit x num-of-variables))
              (bool->bit (apply function (split-bit x num-of-variables)))))))

