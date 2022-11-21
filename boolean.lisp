(defun xor (x y)
  (or (and (not x) y) (and x (not y))))

(defun split-bit (num size)
  (loop for x from (1- size) downto 0
        collect (logbitp x num)))

(defun bool->bit (x)
  (if x 1 0))

(defparameter *binary-operators* '((or 1) (and 2) (xor 2)))
(defparameter *unary-operators* '((not 4)))

(defun weight (c) (second (assoc c *binary-operators*)))
(defun binary-opcode (c) (first (assoc c *binary-operators*)))
(defun unary-opcode (c) (first (assoc c *unary-operators*)))

(defun inf-iter (exp operators operands)
  (cond ((and (null exp) (null operators))
         (first operands))

        ;; implicit multiplication
        ((and exp (or (listp (first exp))
                      (null (weight (first exp)))))
         (inf-iter (cons 'and exp) operators operands))

        ((and exp (or (null operators)
                      (> (weight (first exp)) (weight (first operators)))))
         (inf-aux (rest exp) (cons (first exp) operators) operands))

        (t
         (inf-iter exp (rest operators)
                   (cons (list (binary-opcode (first operators))
                               (cadr operands) (first operands))
                         (cddr operands))))))

(defun inf-aux (exp operators operands)
  (if (and (atom (first exp)) (assoc (first exp) *unary-operators*))
      (inf-iter (cddr exp) operators
                (cons (list (unary-opcode (first exp))
                            (infix->prefix (cadr exp)))
                      operands))
      (inf-iter (rest exp) operators (cons (infix->prefix (first exp)) operands))))

(defun infix->prefix (exp)
  (if (atom exp)
      exp
      (inf-aux exp nil nil)))

(defun notation (exp)
  (let (final stack variables)
    (loop for x across exp
          do (case x
               ((#\') (rplaca final (list 'not (car final))))
               ((#\+) (push 'or final))
               ((#\*) (push 'and final))
               ((#\^) (push 'xor final))
               ((#\() (push final stack) (setf final nil))
               ((#\)) (push final (first stack)) (setf final (pop stack)))
               ((#\0) (push nil final))
               ((#\1) (push t final))
               ((#\space))
               (t (if (alpha-char-p x)
                      (progn (push (read-from-string (string x)) final)
                             (pushnew x variables))
                      (error "wot in tarnation is '~a' doing here" x))))
          finally (return (list (mapcar (lambda (x) (read-from-string (string x)))
                                        (sort variables #'char<=))
                                (infix->prefix final))))))

(defmacro bool-def (name exp)
  `(defun ,name ,@(notation exp)))

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
      (format t "~{~A ~}| ~a~%" (mapcar #'bool->bit (split-bit x num-of-variables))
              (bool->bit (apply function (split-bit x num-of-variables)))))))

