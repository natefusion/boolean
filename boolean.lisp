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

;; modify this to work with the pratt parser
;; (defun notation-alt (exp &optional vars)
;;   (let (final stack variables)
;;     (loop for i from 0 below (length exp)
;;           for x = (char exp i)
;;           do (case x
;;                ((#\~) (push 'not final))
;;                ((#\^) (push 'and final))
;;                ((#\v #\V) (push 'or final))
;;                ((#\>)
;;                 (push 'not final)
;;                 (push 'or final))
;;                ((#\<)
;;                 (if (< i (- (length exp) 2))
;;                     (if (char= (char exp (1+ i)) #\>)
;;                         (let ((lhs (car final))
;;                               ;; wow baddddd
;;                               (rhs (read-from-string (string (char exp (+ 2 i))))))
;;                           (push 'not final)
;;                           (push rhs final)
;;                           (push 'not final)
;;                           (push 'or final)
;;                           (push lhs final)
;;                           (push rhs final)
;;                           (pushnew rhs variables) ;; lame
;;                           (incf i 2)))))
;;                ((#\() (push final stack) (setf final nil))
;;                ((#\)) (push final (first stack)) (setf final (pop stack)))
;;                ((#\f #\c) (push nil final))
;;                ((#\space))
;;                (t (if (alpha-char-p x)
;;                       ;; I need to swap the variable and not here
;;                       ;; If I don't ~a will be '(a not)
;;                       ;; Rather than '(not a)
;;                       ;; there is probably a better way to do this
;;                       (cond ((eql (car final) 'not)
;;                              (pop final)
;;                              (push (read-from-string (string x)) final)
;;                              (pushnew (car final) variables)
;;                              (push 'not final))
;;                             (t
;;                              (push (read-from-string (string x)) final)
;;                              (pushnew (car final) variables)))
;;                       (error "wot in tarnation is '~a' doing here" x))))
;;           finally (return (list (mapcar (lambda (x) (read-from-string (string x)))
;;                                         (sort (union vars variables) #'var<=))
;;                                 (infix->prefix final))))))

(defmacro bool-def (name exp &rest vars)
  `(defun ,name
       ,@(notation exp vars)))

;; notation-alt should work
;; (defmacro bool-def-alt (name exp &rest vars)
;;   `(defun ,name
;;      ,@(notation-alt exp vars)))

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

(defun lhs (exp) (and (listp exp) (second exp)))
(defun rhs (exp) (and (listp exp) (third exp)))
(defun operand (exp) (and (listp exp) (second exp)))
(defun operator (exp) (and (listp exp) (first exp)))

(defun andp (exp) (and (listp exp) (eq (first exp) 'and)))
(defun orp  (exp) (and (listp exp) (eq (first exp) 'or)))
(defun xorp (exp) (and (listp exp) (eq (first exp) 'xor)))
(defun notp (exp) (and (listp exp) (eq (first exp) 'not)))

(defun expr-structure-eq (a b)
  (not (or (and (not (listp a)) (not (listp b)))
           (not (eq (first a) (first b)))
           (or (not (eq (second a) (second b)))
               (not (eq (third a) (third b)))))))

(defun collect-vars (lhs expr &optional vars)
  (cond ((and (consp expr) (consp lhs))
         (loop initially (unless (eq (car lhs) (car expr)) (return nil))
               for x in (rest lhs)
               for y in (rest expr)
               do (if (atom x)
                      ;; t and nil are not variables
                      ;; they must match exactly!!!
                      (if (or (and (eq x t)
                                   (not (eq y t)))
                              (and (eq x nil)
                                   (not (eq y nil))))
                          (return nil)
                          (pushnew `(,x . ,y) vars
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
                                               nil))))
                      (setf vars (collect-vars x y vars)))
               finally (return vars)))
        ;; is this right?? seems so
        ((consp lhs)
         nil)
        ;; this branch ~shouldn't~ ever be taken in a recursive callp
        (t
         ;; t and nil are not variables
         ;; they must match exactly!!!
         (if (or (and (eq lhs t)
                      (not (eq expr t)))
                 (and (eq lhs nil)
                      (not (eq expr nil))))
             nil
             `((,lhs . ,expr))))))

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

(defmacro defaxiom (name lhs rhs)
  `(defun ,name (expr &optional reverse)
     (let ((lhs ',(notate lhs))
           (rhs ',(notate rhs)))
       (when reverse (rotatef lhs rhs))
       (let ((vars (collect-vars lhs expr))) 
         (if vars
             (values (rewrite-vars rhs vars) t)
             ;; nil means false, but it also means the function failed
             ;; this is the reconciliation for that
             (values expr nil))))))

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
                     (loop initially (unless (or (not recurring?) (eq (second exp) 'and)) (format t "("))
                           for x in exp
                           do (second-pass x t)
                           finally (unless (or (not recurring?) (eq (second exp) 'and)) (format t ")"))))
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

(defun flatten (lst rule)
  (labels ((rflatten (lst1 acc)
             (dolist (el lst1)
               (if (funcall rule el)
                   (setf acc (rflatten (cdr el) acc))
                   (push el acc)))
             acc))
    (reverse (rflatten (cdr lst) nil))))

(defun absorption-law-p (a b)
  (or (exp-eq a (lhs b))
      (exp-eq a (rhs b))))

(defun commutative-p (a b)
  (and (exp-eq (lhs a) (lhs b))
       (exp-eq (rhs a) (rhs b)))
  (and (exp-eq (lhs a) (rhs b))
       (exp-eq (rhs a) (lhs b))))

(defun and-associative-p (a b)
  ;; I call make-and here to ensure that the lhs is another and operation, and not just a symbol
  (exp-eq a (make-and (lhs (lhs b)) (make-and (rhs (lhs b)) (rhs b)))))

(defun or-associative-p (a b)
  ;; I call make-or here for the same reason as in and-associative-p
  (exp-eq a (make-or (lhs (lhs b)) (make-or (rhs (lhs b)) (rhs b)))))

(defun exp-eq (a b)
  (cond ((and (orp a) (orp b))
         (or (commutative-p a b)
             (or-associative-p a b)))

        ((and (andp a) (andp b))
         (or (commutative-p a b)
             (and-associative-p a b)))
        ((and (notp a) (notp b))
         (exp-eq (operand a) (operand b)))
        (t
         (eq a b))))

(defun complementp (a b)
  (cond ((notp a)
         (exp-eq (operand a) b))
        ((notp b)
         (exp-eq (operand b) a))
        (t
         nil)))

(defun make-and (a b)
  (cond ((exp-eq a b)
         a)
        ((complementp a b)
         nil)
        ((eq 't b)
         a)
        ((eq 't a)
         b)
        ((or (null a) (null b))
         nil)
        ((and (andp a) (andp b))
         (make-and (make-and a (lhs b)) (rhs b)))
        ((and (or (notp a) (symbolp a)) (or (andp b) (orp b)))
         (make-and b a))
        ;; ((and (andp a) (not (symbolp b)))
        ;;  (make-and (make-and b (lhs a)) (rhs a)))
        ;; ((and (not (symbolp a)) (andp b))
        ;;  (make-and (make-and a (lhs b)) (rhs b)))
        ;; ((orp a)
        ;;  (make-or (make-and (lhs a) b) (make-and (rhs a) b)))
        ;; ((orp b)
        ;;  (make-or (make-and a (lhs b)) (make-and a (rhs b))))
        ;; ((and (andp a) (symbolp b) (find b (flatten a #'andp)))
        ;;  a)
        (t `(and ,a ,b))))

(defun make-or (a b)
  (cond ((exp-eq a b) a)
        ((complementp a b)
         t)
        ((null a)                       ; identity
         b)
        ((null b)                       ; identity
         a)
        ((or (eq 't a) (eq 't b))
         t)
        ((and (orp a) (orp b))
         (make-or (make-or a (lhs b)) (rhs b)))
        ((and (or (notp a) (symbolp a)) (or (andp b) (orp b)))
         (make-or b a))
        ((andp a)
         (cond ((exp-eq (lhs a) b)
                (lhs a))
               ((exp-eq (rhs a) b)
                (rhs a))
               ((complementp (lhs a) b)
                (make-or (rhs a) b))
               ((complementp (rhs a) b)
                (make-or (lhs a) b))
               (t
                `(or ,a ,b))))
        (t
         `(or ,a ,b))))

(defun make-not (a)
  (cond ((notp a)
         (operand a))
        ((eql 't a)
         nil)
        ((null a)
         t)
        ((andp a)
         (make-or (make-not (lhs a)) (make-not (rhs a))))
        (t
         `(not ,a))))

(defun simplify (exp)
  (cond ((andp exp)
         (make-and (simplify (lhs exp))
                   (simplify (rhs exp))))
        ((orp exp)
         (make-or (simplify (lhs exp))
                  (simplify (rhs exp))))
        ((notp exp)
         (make-not (simplify (operand exp))))
        (t exp)))

