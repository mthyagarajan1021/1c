(defvar *rules* (make-hash-table))

(defmacro <- (con &optional ant)
  `(length
     (push (cons (cdr ',con) ',ant)
           (gethash (car ',con) *rules*))))

(defun data0 ()
  (clrhash *rules*)
  (<- (= ?x ?x))
  (<- (parent donald nancy))
  (<- (parent donald debbie))
  (<- (male donald))
  (<- (chain1 ?a ?b)
         (and (= ?a ?b)
              (= ?b ?c)
              (do (show ?c))
              (= ?c 1)))
  (<- (chain2 ?a ?b)
         (and (= ?a ?b)
              (= ?b ?c)
              (>  ?c 0.3)))
  (<- (chain3 ?a ?b)
         (and (= ?a ?b)
              (= ?b ?c)
              (> ?c 3)))
  (<- (chain4 ?a ?b)
         (and (= ?a ?b)
              (= ?b ?c)
              (not (> ?c 3))
              (= ?c 1)))
  (<- (father ?x ?y) 
      (and 
        (parent ?x ?y) 
        (male ?x)))
  (<- (sibling ?x ?y) 
      (and (parent ?z ?x)
           (parent ?z ?y)
           (not(= ?x ?y)) ;check that same person is not being compared
       )
    ))


;--------- --------- --------- --------- --------- --------- ---------
(defun test1 ()
  (data0)
  (query 
    (father ?x ?y)
    (format t "~A is the father of ~A~%" ?x ?y))
  (query 
    (sibling ?x ?y)
    (format t "~A is the sibling of ~A.~%" ?x ?y))
  (query 
    (chain1 ?x 1)
    (format t "?x in chain1 matches to ~A.~%" ?x))
  (query 
    (chain2 ?x 1)
    (format t "?x in chain2 matches to ~A.~%" ?x))
  (query 
    (chain3 ?x 1)
    (format t "?x in chain3 matches to ~A.~%" ?x))
  (query 
    (chain4 ?x 1)
    (format t "?x in chain4 matches to ~A.~%" ?x))
)
    
;--------- --------- --------- --------- --------- --------- ---------
(defun unify (x y &optional binds)
  (cond 
    ((eql x y)        (values binds t))
    ((assoc x binds)  (unify (known x binds) y binds))
    ((assoc y binds)  (unify x (known y binds) binds))
    ((var? x)         (values (cons (cons x y) binds) t))
    ((var? y)         (values (cons (cons y x) binds) t))
    (t
      (when (and (consp x) (consp y))
        (multiple-value-bind (b2 yes) 
          (unify (car x) (car y) binds)
          (and yes (unify (cdr x) (cdr y) b2)))))))

(defun var? (x)
  (and (symbolp x) 
       (eql (char (symbol-name x) 0) #\?)))

;; does no occur check cause crash?
;--------- --------- --------- --------- --------- --------- ---------
(defmacro query (question &body body)
  (let ((binds (gensym)))
    `(dolist (,binds (prove ',question))
       (let ,(mapcar (lambda (v)
                         `(,v (known ',v ,binds)))
         (has-vars question))
   ,@body))))

(defun prove (expr &optional binds)
  (case (car expr)
    (and  (ands        (reverse (cdr expr))   binds))
    (or   (ors         (cdr  expr)            binds))
    (not  (negation    (cadr expr)            binds))
    (do   (evals       (cadr expr)            binds))
    (show   (prove1       (car  expr) (cdr expr) binds))
    (>   (>       (car  expr) (cdr expr) binds))
    (<   (<       (car  expr) (cdr expr) binds))
    (>=                                        )
    (<=                                        )
    (t    (prove1      (car  expr) (cdr expr) binds))))

;--------- --------- --------- --------- --------- --------- ---------
;code for 2B
(defun has-vars(lst)
      (let ((out))
        (labels (
           (collect-r(lst fn)
             (if (atom lst)
                  (if (funcall fn lst)
                      (push lst out))
                  (dolist ( y lst)
                     (collect-r y fn)))))
           (collect-r lst #'var?)
           (remove-duplicates out))))

;--------- --------- --------- --------- --------- --------- ---------
;code for 2A
; (known '?a '((?b . 3) (?a. ?b) ))
(defun known (a lst)
   (let ((tmp (assoc a lst)))
        (if tmp
            (known (cdr tmp) lst)
            a)))
;--------- --------- --------- --------- --------- --------- ---------
;code for 3A since 'show' didnt exist?
;Added 'show' to prove function, LINE 92. Is that how it works?
(defun show(x)
  (print x)
  )
;--------- --------- --------- --------- --------- --------- ---------
(defun ands (goals binds)
  (if (null goals)
      (list binds)
      (mapcan (lambda (b)
                  (prove (car goals) b))
              (ands (cdr goals) binds))))

(defun ors(goals binds)
  (mapcan (lambda (c) (prove c binds))
          goals))

(defun negation (goal binds)
  (unless (prove goal binds)
    (list binds)))

(defun evals (expr binds)
  " turns e.g. (print (list ?a ?b)) into
    (let ((?a x) ; where x is computed from (known ?a binds)
          (?b y)); where y is computed from (known ?b binds)
      (print ?a ?b))"
  (labels 
    ((local-vars ()
        (mapcar 
          (lambda (x) 
                 `(,x ',(known x binds))) 
             (has-vars expr))))
    (eval `(let ,(local-vars) 
              ,expr))
    (list binds)))

(defun prove1 (pred args binds)
  (mapcan 
    (lambda (r)
        (multiple-value-bind (b2 yes) 
          (unify args (car r) 
                 binds)
          (when yes
            (if (cdr r)  
              (prove (cdr r) b2) 
              (list b2)))))
    (mapcar #'renames
            (gethash pred *rules*))))

;--------- --------- --------- --------- --------- --------- ---------

(defun renames (r)
  (sublis (mapcar (lambda (v) (cons v (gensym "?")))
                  (has-vars r))
          r))


(test1)
