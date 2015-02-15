#lang racket
(require racket/set)
(require racket/dict)

; ('equal t1 t2)
; ('implicit t1 m t2)
; ('explicit t1 t2)

(define create_fresh_type_variable
  ((lambda (ctr)
     (lambda ()
       (set! ctr (+ ctr 1))
       ctr)) 0))

;; type environment
(define (get_type exp)
  (cond ((number? exp) 'int)
        ((string? exp) 'string)
        ((boolean? exp) 'boolean)))

;; types
(define type_var? number?)
(define type_con? symbol?)
(define (type_fun? type) (and (pair? type) (eq? (car type) '->)))
(define (type_scheme? type) (and (pair? type) (eq? (car type) 'scheme)))
  
; Bottom up constraint collector: (assumption constraints type)
(define (bottom_up exp monos)
  (if (pair? exp)
      (case (car exp)
        [(lambda) (bottom_up_abs exp monos)]
        [(let)    (bottom_up_let exp monos)]
        [else     (bottom_up_app exp monos)])
      (if (symbol? exp)
          (bottom_up_var exp)
          (bottom_up_lit exp))))

; [Var]
(define (bottom_up_var x)
  (let ((beta (dict-ref environment x (lambda () (create_fresh_type_variable)))))
    (list (mutable-set (cons x beta)) (mutable-set) beta)))

; [App]
(define (bottom_up_app exp monos)
  (let ((e1 (car exp))
        (e2 (cadr exp))
        (beta (create_fresh_type_variable)))
    (match-define (list a1 c1 t1) (bottom_up e1 monos))
    (match-define (list a2 c2 t2) (bottom_up e2 monos))
    (set-union! a1 a2)
    (set-union! c1 c2 (set (list 'equal t1 (list '-> t2 beta))))
    (list a1 c1 beta)))

; [Abs]
(define (bottom_up_abs exp monos)
  (let ((x (caadr exp))
        (e (caddr exp))
        (beta (create_fresh_type_variable))
        (c (mutable-set))
        (a2 (mutable-set)))
    (match-define (list a c t) (bottom_up e (set-add monos x)))
    (set-for-each a (lambda (y)
                      (if (eq? (car y) x)
                          (set-add! c (list 'equal (cdr y) beta))
                          (set-add! a2 y))))
    (list a2 c (list '-> beta t))))

; [Let]
(define (bottom_up_let exp monos)
  (let ((x (car (caadr exp)))
        (e1 (cadr (caadr exp)))
        (e2 (caddr exp)))
    (match-define (list a1 c1 t1) (bottom_up e1 monos))
    (match-define (list a2 c2 t2) (bottom_up e2 monos))
    (set-union! c1 c2)
    (set-for-each a2 (lambda (a)
                       (if (eq? (car a) x)
                           (set-add! c1 (list 'implicit (cdr a) t1 monos))
                           (set-add! a1 a))))
    (list a1 c1 t2)))


; [Lit]
(define (bottom_up_lit exp)
  (list (mutable-set)
        (mutable-set)
        (cond ((number?  exp) 'int)
              ((string?  exp) 'string)
              ((boolean? exp) 'boolean)
              (else 'unknown))))





;; Solver: list(constraint) -> subsitution
(define (solve constraints)
  (if (empty? constraints)
      sub_empty
      (let ((constraint (car constraints)))
        (case (car constraint)
          [(equal)
           (let ((s (mgu (cadr constraint) (caddr constraint))))
             (subs-union (solve (sub_constraints s (cdr constraints)))
                         s))]
          [(implicit)
           (match-define (list _ t1 t2 monos) constraint)
           (if (set-empty? (set-intersect (set-subtract (free_vars t2)
                                                           monos)
                                      (active_vars (cdr constraints))))
               (solve (cons (list 'explicit t1 (generalize monos t2))
                            (cdr constraints)))
               (raise "type error"))]
          [(explicit)
           (match-define (list _ t s) constraint)
           (solve (cons (list 'equal t (instantiate s))
                        (cdr constraints)))]))))


;; dict -> dict -> dict
(define (subs-union subs1 subs2)
  (let ((s (dict-map subs2
                      (lambda (v t)
                        (cons v (substitute subs1 t))))))
    (dict-for-each subs1
                   (lambda (v t)
                     (when (dict-ref subs2 v #f)
                       (raise "substitutions with same tvars"))
                     (set! s (dict-set s v t))))
    s))


(define sub_empty '())

;; type -> substitution -> type
(define (substitute s type)
  (cond ((type_con? type)
         type)
        ((type_var? type)
         (dict-ref s type type))
        ((type_fun? type)
         (list '->
               (substitute s (cadr type))
               (substitute s (caddr type))))
        (else (raise (string-append "unknown type: " type)))))

;;  substitution -> constraint -> constraint
(define (sub_constraint s constraint)
  (case (car constraint)
    [(equal) (list 'equal
                   (substitute s (cadr constraint))
                   (substitute s (caddr constraint)))]
    [(implicit) (list 'implicit
                               (substitute s (cadr constraint))
                               (substitute s (caddr constraint))
                               (for/set ([var (cadddr constraint)])
                                 (dict-ref s var var)))]
    [(explicit) (list 'explicit
                               (substitute s (cadr constraint))
                               (substitute s (caddr constraint)))]))
 
;; substitution -> list(constraint) -> list(constraint)
(define (sub_constraints s constraints)
  (map (lambda (c) (sub_constraint s c)) constraints))
  
;; generalize: set(type var) -> type -> scheme
(define (generalize monos type)
  (list 'scheme (set-subtract (free_vars type) monos) type))

;; instantiate: scheme -> type
(define (instantiate scheme)
  (match-define (list _ qs type) scheme)
  (substitute (for/list ([q qs]) (cons q (create_fresh_type_variable))) type))
  

;; free variables: type -> set
(define (free_vars t)
  (cond ((type_var? t) (set t)) 
        ((type_fun? t)
         (set-union (free_vars (cadr t)) (free_vars (caddr t))))
        ((type_con? t) (set))
        (else (raise "unknown type " t))))

  
;; active variables: constraints -> set(type var)
(define (active_vars constraints)
  (foldl (lambda (constraint nxt)
                     (case (car constraint)
                       [(equal) (set-union (set (free_vars (cadr constraint)) (free_vars (caddr constraint)))
                                           nxt)]
                       [(implicit) (set-union (set-union (free_vars (cadr constraint))
                                                       (set-intersect (caddr constraint)
                                                                      (free_vars (cadddr constraint))))
                                              nxt)]
                       [(explicit) (set-union (set-union (free_vars (cadr constraint))
                                                       (free_vars (caddr constraint)))
                                              nxt)]))
       (set) constraints))

;; most general unifier: type -> type -> substitution
(define (mgu t1 t2)
  (cond ((and (pair? t1) (pair? t2))
      (match-let* (((list _ t1l t1r) t1)
                   ((list _ t2l t2r) t2)
                   (s1 (mgu t1l t2l))
                   (s2 (mgu (substitute s1 t1r) (substitute s1 t2r))))
        (set-union s1 s2)))
        ((number? t1)
         (varbind t1 t2))
        ((number? t2)
         (varbind t2 t1))
        (else 'error)))

(define (varbind var type)
  (cond ((equal? var type) sub_empty)
        ((set-member? (free_vars type) var) (list 'infinite-type var type))
        (else (list (cons var type)))))
         
    
;(define environment
;  '((+ . (-> (int int) int))
;    (- . (-> (int int) int))
;    (* . (-> (int int) int))
;    (/ . (-> (int int) int))
;    (< . (-> (int int) boolean))
;    (= . (-> (int int) boolean))))

(define (infer exp)
  (match-define (list assumptions constraints type) (bottom_up exp (set)))
  (print-inferred exp (list assumptions constraints (solve (set->list constraints)) type)))


(define (print-inferred exp result)
  (match-define (list assumptions constraints substitutions type) result)
  (displayln (list exp ':= (substitute substitutions type)))
  (displayln substitutions)
  )
  
  

; test
(define e1 'x)
(define e2 '(lambda (x) x))
(define e3 '(x 2))
(define e4 '((lambda (x) x) 2))
(define e5 '(let ((x 2)) x))
;(define e6 '(let ((x 2)) (+ x x)))
(define e7 '(lambda (x) (let ((x 2)) x)))
;(define e8 '(lambda (x) (let ((x 2)) (+ x x))))


(infer e1)
(infer e2)
(infer e3)
(infer e4)
(infer e5)
(infer e6)
(infer e7)
(infer e8)
           