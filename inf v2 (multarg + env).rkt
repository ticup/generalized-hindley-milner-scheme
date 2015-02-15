#lang racket
(require racket/set)
(require racket/dict)

; ('equal t1 t2)
; ('implicit t1 t2 m)
; ('explicit t1 t2)

(define ctr 0)
(define (reset_var_ctr!) (set! ctr 0))
(define (create_fresh_type_variable name)
  (set! ctr (+ ctr 1))
  (string-append (if (symbol? name) (symbol->string name) name) (number->string ctr)))

;; type environment
(define (get_type exp)
  (cond ((number? exp) 'int)
        ((string? exp) 'string)
        ((boolean? exp) 'boolean)))

;; types
; 1
; 'int
; (-> (t1 t2 tn) tr)
; ('scheme (q1 q2 qn) t)
(define type_var? string?)
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
  (let ((type (dict-ref environment x #f)))
    (if type
        (list (mutable-set) (mutable-set) type)
        (let ((beta (create_fresh_type_variable x)))
          (list (mutable-set (cons x beta)) (mutable-set) beta)))))

; [App]
(define (bottom_up_app exp monos)
  (let ((e1 (car exp))
        (args (cdr exp))
        (beta (create_fresh_type_variable "app")))
    (match-define (list a1 c1 t1) (bottom_up e1 monos))
    (define argtypes
      (for/list [(arg args)]
        (match-define (list a2 c2 t2) (bottom_up arg monos))
        (set-union! a1 a2)
        (set-union! c1 c2)
        t2))
    (set-union! c1 (set (list 'equal t1 (list '-> argtypes beta))))
    (list a1 c1 beta)))

; [Abs]
(define (bottom_up_abs exp monos)
  (let* ((args (cadr exp))
         (e (caddr exp))
         (abs (map (lambda (x) (cons x (create_fresh_type_variable "arg"))) args))
         (bs (map (lambda (ab) (cdr ab)) abs))
         (c (mutable-set))
         (a2 (mutable-set)))
    (match-define (list a c t) (bottom_up e (set-union monos (list->set args))))
    (set-for-each a (lambda (y)
                      (let ((beta (assoc (car y) abs)))
                        (if beta
                            (set-add! c (list 'equal (cdr y) (cdr beta)))
                            (set-add! a2 y)))))
    (list a2 c (list '-> bs t))))

; [Let]
(define (bottom_up_let exp monos)
  (let ((x (car (caadr exp)))
        (e1 (cadr (caadr exp)))
        (e2 (caddr exp)))
    (match-define (list a1 c1 t1) (bottom_up e1 monos))
    (match-define (list a2 c2 t2) (bottom_up e2 monos))
    (set-union! c1 c2)
    (set-for-each a2 (lambda (a)
                       (if (equal? (car a) x)
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
               (solve (append (cdr constraints) (list constraint))))]
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
               (map (lambda (x) (substitute s x)) (cadr type))
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
  (substitute (for/list ([q qs]) (cons q (create_fresh_type_variable "I"))) type))
  

;; free variables: type -> set
(define (free_vars t)
  (cond ((type_var? t) (set t)) 
        ((type_fun? t)
         (set-union (list->set (map (lambda (x) (free_vars x)) (cadr t))) (free_vars (caddr t))))
        ((type_con? t) (set))
        (else (/ 1 0))))

  
;; active variables: constraints -> set(type var)
(define (active_vars constraints)
  (foldl (lambda (constraint nxt)
                     (case (car constraint)
                       [(equal) (set-union (set-union (free_vars (cadr constraint)) (free_vars (caddr constraint)))
                                           nxt)]
                       [(implicit) (set-union (set-union (free_vars (cadr constraint))
                                                         (set-intersect (cadddr constraint)
                                                                        (free_vars (caddr constraint))))
                                              nxt)]
                       [(explicit) (set-union (set-union (free_vars (cadr constraint))
                                                         (free_vars (caddr constraint)))
                                              nxt)]))
       (set) constraints))

;; most general unifier: type -> type -> substitution
(define (mgu t1 t2)
  (cond ((and (pair? t1) (pair? t2))
      (match-let* (((list _ t1params t1r) t1)
                   ((list _ t2params t2r) t2))
        (if (not (eq? (length t1params) (length t2params)))
            (raise "incompatible arguments")
            (let ((s (for/fold ([s sub_empty])
                               ([p1 t1params] [p2 t2params])
                       (set-union (mgu (substitute s p1) (substitute s p2))
                                  s))))
              (set-union (mgu (substitute s t1r) (substitute s t2r))
                         s)))))
        ((equal? t1 t2) sub_empty)
        ((type_var? t1)
         (varbind t1 t2))
        ((type_var? t2)
         (varbind t2 t1))
        (else (/ 1 0))))

(define (varbind var type)
  (cond ((equal? var type) sub_empty)
        ((set-member? (free_vars type) var) (list 'infinite-type var type))
        (else (list (cons var type)))))
      
         
    
(define environment
  '((+ . (-> (int int) int))
    (- . (-> (int int) int))
    (* . (-> (int int) int))
    (/ . (-> (int int) int))
    (< . (-> (int int) boolean))
    (= . (-> (int int) boolean))))

(define (infer exp)
  (match-define (list assumptions constraints type) (bottom_up exp (set)))
  (list assumptions constraints type (solve (set->list constraints))))

(define (p-infer exp)
  (reset_var_ctr!)
  (match-define (list assumptions constraints type substitutions) (infer exp))
  (displayln (list exp ':= (substitute substitutions type)))
  (displayln substitutions)
  (displayln "-----------------------------------------------------------------"))

(define (p*-infer exp)
  (reset_var_ctr!)
  (match-define (list assumptions constraints type substitutions) (infer exp))
  (displayln (list exp ':= (substitute substitutions type)))
  (for ([s substitutions])
    (displayln s))
  (displayln "-----------------------------------------------------------------"))
  

; test
(define e1 'x)
(define e2 '(lambda (x) x))
(define e3 '(x 2))
(define e4 '((lambda (x) x) 2))
(define e5 '(let ((x 2)) x))
(define e6 '(let ((x 2)) (+ x x)))
(define e7 '(lambda (x) (let ((x 2)) x)))
(define e8 '(lambda (x) (let ((x 2)) (+ x x))))
(define e9 '(lambda (x y) (let ((x 2)) (+ x x))))
(define e10 '(let ((x (lambda (x y) (let ((x 2)) (+ x x))))) (x "foo" "bar")))
(define e11 '(let ((f (lambda (x) (lambda (y) (+ x 1)))))
               (let ((g (f 2))) g)))


(p-infer e1)
(p-infer e2)
(p-infer e3)
(p-infer e4)
(p-infer e5)
(p-infer e6)
(p-infer e7)
(p-infer e8)
(p-infer e9)
(p*-infer e10)
(p*-infer e11)
           