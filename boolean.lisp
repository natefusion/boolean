(defpackage boolean
  (:use :cl))

(in-package :boolean)

(defun xor (x y)
  (or (and (not x) y) (and x (not y))))

(defun split-bit (num size)
  (loop for x from (1- size) downto 0
        collect (logbitp x num)))

(defun bool->bit (x)
  (if x 1 0))

(defun vars (symbol)
  (case symbol
    (a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7) (h 8) (i 9) (j 10)
    (k 11) (l 12) (m 13) (n 14) (o 15) (p 16) (q 17) (r 18) (s 19) ((t) 20)
    (u 21) (v 22) (w 23) (x 24) (y 25) (z 26)
    (t (error "'~a' is not a valid variable" symbol))))

(defun var<= (symbol1 symbol2)
  (<= (vars symbol1) (vars symbol2)))

(defun notation (exp &optional vars)
  (let (variables)
    (labels ((infix-binding-power (op)
               (case op
                 (or (values 1 2))
                 ((and xor) (values 3 4))
                 (|)| (values nil nil '|)|))
                 (t (values 3 4 'implicit-*))))
             (postfix-binding-power (op)
               (case op
                 (not 10)
                 (t nil)))
             (infix->prefix (min-bp)
               (loop with lhs = (let ((lhs (pop exp)))
                                  (case lhs
                                    (|(| (prog1 (infix->prefix 0)
                                           (unless (eq (pop exp) '|)|)
                                             (error "No closing parenthesis somewhere lol"))))
                                    ((or and xor) (list lhs (infix->prefix lhs)))
                                    (t lhs)))
                     for op = (car exp)
                     do (unless op (loop-finish))
                        (block thing
                          (multiple-value-bind (lhs-bp) (postfix-binding-power op)
                            (when lhs-bp
                              (when (< lhs-bp min-bp)
                                (loop-finish))
                              (pop exp)
                              (setf lhs (list op lhs))
                              (return-from thing)))
                          (multiple-value-bind (lhs-bp rhs-bp special) (infix-binding-power op)
                            (cond ((or (eq special '|)|) (< lhs-bp min-bp))
                                   (loop-finish))
                                  ((eq special 'implicit-*)
                                   (setf op 'and))
                                  (t
                                   (pop exp)))
                            (setf lhs (list op lhs (infix->prefix rhs-bp)))))
                     finally (return lhs)))
             (lex (exp)
               (loop for x across exp
                     append (if (alpha-char-p x)
                                (let ((a (read-from-string (string x))))
                                  (pushnew a variables)
                                  (list a))
                                (case x
                                  ((#\') '(not))
                                  ((#\+) '(or))
                                  ((#\*) '(and))
                                  ((#\^) '(xor))
                                  ((#\() '(|(|))
                                  ((#\)) '(|)|))
                                  ((#\0) '(nil))
                                  ((#\1) '(t))
                                  ((#\space))
                                  (t (error "wot in tarnation is '~a' doing here" x)))))))
      (setf exp (lex exp))
      (list (mapcar (lambda (x) (read-from-string (string x)))
                    (sort (union vars variables) #'var<=))
            (infix->prefix 0)))))

(defun notate (exp &optional vars)
  (second (notation exp vars)))

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

(defun collect-vars (lhs expr)
  (let ((vars nil))
    (labels ((same-operation (x y)
               (and (consp x) (consp y) (eq (car x) (car y))))
             (t-and-nil-check (x y)
               "t and nil are not variables, they must match exactly"
               (and (or (not (eq x t))
                        (eq y t))
                    (or (not (eq x nil))
                        (eq y nil))))
             (recur (lhs expr)
               (loop for x in (rest lhs)
                     for y in (rest expr)
                     do (if (atom x)
                            ;; t and nil are not variables
                            ;; they must match exactly!!!
                            (if (t-and-nil-check x y)
                                (pushnew (cons x y) vars
                                         ;; aaaaah
                                         ;; this fixes the idempotent case
                                         ;; when the expression is not idempotent
                                         ;; lhs:    x^x
                                         ;; expr:   a^b
                                         ;; !! x cannot equal a and b at the same time !!
                                         ;; result: a^b
                                         ;; ------
                                         ;; lhs:    x^x
                                         ;; expr:   a^a
                                         ;; !! x equals a and x equals a. all good !!
                                         ;; result: a
                                         :test (lambda (x y)
                                                 (if (eq (car x) (car y))
                                                     (if (tree-equal (cdr x) (cdr y))
                                                         t
                                                         (return-from collect-vars nil))
                                                     nil)))
                                (return-from collect-vars nil))
                            (if (same-operation x y)
                                (recur x y)
                                (return-from collect-vars nil))))))
      (cond ((same-operation lhs expr)
             (recur lhs expr)
             vars)
            ((t-and-nil-check lhs expr)
             (list (cons lhs expr)))
            (t
             nil)))))

(defun rewrite-vars (rhs vars)
  (cond ((null rhs)
         nil)
        ((eq rhs t)
         t)
        ((atom rhs)
         (cdr (assoc rhs vars)))
        (t
         (loop for x in rhs
               for match = (assoc x vars)
               if match
                 collect (cdr match)
               else if (listp x)
                      collect (rewrite-vars x vars)
               else
                 collect x))))

(defun fancy-term-rewriter (lhs rhs expr)
  (let ((vars (collect-vars lhs expr)))
    (if vars
        (values (rewrite-vars rhs vars) t)
        (values expr nil))))

(defmacro defaxiom (name lhs rhs)
  `(defun ,name (expr &optional reverse)
     (let ((lhs ',(notate lhs))
           (rhs ',(notate rhs)))
       (if (not reverse)
           (fancy-term-rewriter lhs rhs expr)
           (fancy-term-rewriter rhs lhs expr)))))

;; https://en.wikipedia.org/wiki/Boolean_algebra#Laws
;; https://en.wikipedia.org/wiki/Rewriting
;; https://en.wikipedia.org/wiki/Computer_algebra
;; https://en.wikipedia.org/wiki/Boolean_satisfiability_problem
;; https://en.wikipedia.org/wiki/SAT_solver

(defaxiom or-commutative "x+y"     "y+x")
(defaxiom or-associative "x+(y+z)" "(x+y)+z")
(defaxiom or-identity    "x+0"     "x")
(defaxiom or-annihilator "x+1"     "1")
(defaxiom or-idempotence "x+x"     "x")

(defaxiom and-commutative "xy"    "yx")
(defaxiom and-associative "x(yz)" "(xy)z")
(defaxiom and-identity    "x1"    "x")
(defaxiom and-annihilator "x0"    "0")
(defaxiom and-idempotence "xx"    "x")

(defaxiom absorption-1   "x(x+y)" "x")
(defaxiom absorption-2   "x+xy"   "x")
(defaxiom distributive-1 "x(y+z)" "xy+xz")
(defaxiom distributive-2 "x+yz"   "(x+y)(x+z)")

(defaxiom complementation-1 "xx'"  "0")
(defaxiom complementation-2 "x+x'" "1")

(defaxiom demorgan-1 "x'y'"  "(x+y)'")
(defaxiom demorgan-2 "x'+y'" "(xy)'")

(defaxiom involution "x''" "x")

(defun prefix->infix (exp)
  (labels ((first-pass (exp &optional op)
             (cond ((atom exp) exp)
                   ((case (car exp) ((or and not) t))
                    (first-pass (cdr exp) (car exp)))
                   (t (let ((next (first-pass (cdr exp) op)))
                        (cons (first-pass (car exp)) (when next (cons op next)))))))
           (second-pass (exp recurring?)
             (if (listp exp)
                 (if (= 1 (length exp))
                     (format t "~a'" (car exp))
                     (loop initially (unless (not recurring?) (format t "("))
                           for x in exp
                           do (second-pass x t)
                           finally (unless (not recurring?) (format t ")"))))
                 (case exp
                   (and
                    ;; do nothing
                    )                
                   (or (format t "+"))
                   (t (format t "~a" exp))))))
    (second-pass (first-pass exp) nil)))

(defun super-apply (functions argument)
  (if (null functions)
      argument
      (list (car functions) (super-apply (cdr functions) argument))))

(defmacro transform (expression &body transformations-to-apply)
  `(prefix->infix ,(super-apply (reverse transformations-to-apply) `',(notate expression))))
