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

(defun vars (symbol)
  (case symbol
    (a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7) (h 8) (i 9) (j 10)
    (k 11) (l 12) (m 13) (n 14) (o 15) (p 16) (q 17) (r 18) (s 19) ((t) 20)
    (u 21) (v 22) (w 23) (x 24) (y 25) (z 26)
    (t (error "'~a' is not a valid variable" symbol))))

(defun var<= (symbol1 symbol2)
  (<= (vars symbol1) (vars symbol2)))

(defun notation (exp &optional vars)
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
                             (pushnew (car final) variables))
                      (error "wot in tarnation is '~a' doing here" x))))
          finally (return (list (mapcar (lambda (x) (read-from-string (string x)))
                                        (sort (union vars variables) #'var<=))
                                (infix->prefix final))))))

(defmacro bool-def (name exp &rest vars)
  `(defun ,name
       ,@(notation exp vars)))

(defun the-same (f1 f2)
  (let ((num-of-variables-f1 (length (sb-introspect:function-lambda-list f1)))
        (num-of-variables-f2 (length (sb-introspect:function-lambda-list f2))))
    
    (when (/= num-of-variables-f1 num-of-variables-f2)
      (return-from the-same nil))

    (dotimes (x (expt 2 num-of-variables-f1) t)
      (unless (eq (apply f1 (split-bit x num-of-variables-f1))
                  (apply f2 (split-bit x num-of-variables-f1)))
        (return-from the-same nil)))))

(defun truth-table (function &optional range)
  (let* ((lambda-list (sb-introspect:function-lambda-list function))
         (num-of-variables (length lambda-list))
         (num-of-rows (if range range (expt 2 num-of-variables))))
    
    (format t "~{~A ~}~%"  lambda-list)

    (dotimes (x num-of-rows)
      (format t "~{~A ~}| ~a~%" (mapcar #'bool->bit (split-bit x num-of-variables))
              (bool->bit (apply function (split-bit x num-of-variables)))))))

