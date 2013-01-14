;; Hindley-Milner type inference
;; From "Interpreting types as abstract values." (Oleg Kiselyov and Chung-chieh Shan) 
;; Formosan Summer School on Logic, Language, and Computation July 9–10, 2008.
;; URL: http://okmij.org/ftp/Computation/FLOLAC/lecture.pdf

#!r6rs
(library (unweave type-inference)
         (export infer-types)

         (import (rnrs)
                 (rnrs eval)

                 (only (ikarus) set-car!)
                 (only (scheme-tools) pretty-print symbol-maker)

                 (scheme-tools srfi-compat :69)
                 (scheme-tools srfi-compat :1)

                 (scheme-tools math)

                 (unweave external normal-interpreter)
                 (unweave external labeling)
                 (unweave external church-syntax)

                 (unweave z3)

                 (unweave util))
         
(define (first-letter x)
  (string->symbol (substring (symbol->string x) 0 1)))

;; Our data structures
;; data Type = {prim} | (-> Type Type) | TVAR | ({parametric-type} {type-parameters-or-variables})

(define (type? t)
  (or (primitive-type? t)
      (type-variable? t)
      (arrow-type? t)
      (parametric-type? t)))

(define (primitive-type? t)
  (and (symbol? t)
       (member t '(Int Bool Real Lst))))

(define (type-variable? t)
  (and (symbol? t)
       (equal? 'T (first-letter t))))

(define (arrow-type? t)
  (and (pair? t)
       (equal? '-> (car t))))
(define (arrow-type-arg t) (cadr t))
(define (arrow-type-res t) (caddr t))

(define (parametric-type? t)
  (and (pair? t)
       (member (car t) '(Lst))))
(define (parametric-type-constructor t)
  (car t))
(define (parametric-type-parameters t)
  (cdr t))


;; Type variable environments

(define (make-TVE)
  (make-hash-table equal?))

(define (tv-lookup tve tvar)
  (if (hash-table-exists? tve tvar) 
    (hash-table-ref tve tvar)
    '()))

(define (tv-extend tve tvar type)
  (hash-table-set! tve tvar type)
  tve)

(define (tv-sub tve type)
  (cond [(arrow-type? type) `(-> ,(arrow-type-arg type) ,(arrow-type-res type))]
        [(type-variable? type) (let* ([t (tv-lookup tve type)])
                                 (if (null? t) type
                                   (tv-sub tve t)))]
        [else type]))

(define (tv-chase tve type)
  (cond [(type-variable? type) (let* ([t (tv-lookup tve type)])
                                 (if (null? t) type
                                   (tv-chase tve type)))]
        [else type]))

;; Unification

(define (unify t1 t2 tve)
  (unify* (tv-chase tve t1) (tv-chase tve t2) tve))

(define (unify* t1 t2 tve)
  (cond [(and (primitive-type? t1)
              (primitive-type? t2)
              (equal? t1 t2))
         tve]
        [(and (arrow-type? t1)
              (arrow-type? t2))
         (let ([res1 (unify (arrow-type-arg t1) (arrow-type-arg t2) tve)])
           (if (equal? 'MISMATCH res1) res1
             (let ([res2 (unify (arrow-type-res t1) (arrow-type-res t2) res1)])
               res2)))]
        [(and (parametric-type? t1)
              (parametric-type? t2)
              (equal? (parametric-type-constructor t1)
                      (parametric-type-constructor t2)))
         (letrec ([loop (lambda (t1 t2 env)
                          (let ([res (unify (car t1) (car t2) env)])
                            (if (equal? 'MISMATCH res) res
                              (loop (cdr t1) (cdr t2) res))))])
           (loop (cdr t1) (cdr t2) tve))]
        [(type-variable? t1) (unify-variables t1 t2 tve)]
        [(type-variable? t2) (unify-variables t2 t1 tve)]
        [else (begin
                (pretty-print `(mismatch ,t1 ,t2))
                'MISMATCH)]))

(define (unify-variables tvar type tve)
  (pretty-print 'unify-variables)
  (cond [(type-variable? type)
         (if (equal? type tvar)
           tve
           (tv-extend tve tvar type))]
        [else (if (occurs tvar type tve)
                'OCCURS-CHECK
                (tv-extend tve tvar type))]))

(define (occurs tvar type tve)
  (cond [(primitive-type? type) #f]
        [(arrow-type? type)
         (or (occurs tvar (arrow-type-arg type) tve)
             (occurs tvar (arrow-type-res type) tve))]
        [(parametric-type? type)
         (letrec ([loop (lambda (params)
                          (or (occurs tvar (car params) tve)
                              (loop (cdr params))))])
           (loop (parametric-type-parameters type)))]
        [(type-variable? type)
         (if (hash-table-exists? tve type)
           (occurs tvar (tv-lookup tve type) tve)
           (equal? tvar type))]
        [else #f]))

;; Term-variable->type environments

(define (tenv-lkup tenv v)
  (cdr (assoc v tenv)))

(define (tenv-ext tenv var val)
  (cons (cons var val) tenv))

(define (tenv-ext-multiple tenv var-vals)
  (append var-vals tenv))

;; The abstract interpreter

(define (infer-types expr tenv)

  (define tve (make-TVE))

  (define type-variable-ctr 0)
  
  (define (reset-type-variable-ctr!)
    (set! type-variable-ctr 0))
  
  (define (next-type-variable!)
    (let* ([next-type-variable (string->symbol (string-append "T" (number->string type-variable-ctr)))])
      (set! type-variable-ctr (+ 1 type-variable-ctr))
      next-type-variable))

  (define (unify! t1 t2)
    (let ([unify-result (unify t1 t2 tve)])
      (set! tve unify-result)))

  ;; the types associated with labels must be the most-grounded types
  (define label-type-map '())
  (define (add-type! l t)
    (set! label-type-map 
      (cons (cons l t) label-type-map)))

  (define (tv-sub-all)
    (map (lambda (label-type)
           (cons (car label-type)
                 (tv-sub tve (cdr label-type))))
         label-type-map))

  (define (get-type v)
    (cond [(number? v) (if (exact? v) 'Int 'Real)]
          [(null? v) 'Lst]
          [else 'UNKNOWN]))

  (define (T ex env)
    (cond [(if? ex)
           (explode-if ex (lambda (l c t e)
                            (let* ([Tc (T c env)]
                                   [Te (T e env)]
                                   [Tt (T t env)])
                              (unify! Tc 'Bool)
                              (unify! Te Tt)
                              (add-type! l Tt)
                              Tt)))]
          [(lambda? ex) 
           (explode-lambda ex (lambda (l vs call)
                                (let* ([new-tvars (map (lambda (v) (next-type-variable!)) vs)]
                                       [Te (T call (tenv-ext-multiple tenv
                                                                      (map (lambda (v tv)
                                                                             (cons v tv))
                                                                           vs new-tvars)))]
                                       [final-type (fold (lambda (next-type acc)
                                                           `(-> ,next-type ,acc))
                                                         Te
                                                         (reverse new-tvars))])
                                  
                                  (add-type! l final-type)
                                  final-type)))]
          [(letrec? ex)
           (explode-letrec  ex (lambda (l bs call)
                                 (let* ([local-binding-env
                                          (fold (lambda (b e)
                                                  (tenv-ext env 
                                                            (car b) 
                                                            (T (cadr b) e)))
                                                env bs)]
                                        [final-type (T call local-binding-env)])
                                   (add-type! l final-type)
                                   final-type)))]
          [(call? ex)
           (explode-call ex (lambda (l f vs)
                              (let* ([Tf (T f env)]
                                     [Tvs (map (lambda (v) (T v env)) vs)]
                                     [Tv-res (next-type-variable!)])
                                (unify! Tf (fold (lambda (next-type acc)
                                                   `(-> ,next-type ,acc))
                                                 Tv-res
                                                 (reverse Tvs)))
                                (add-type! l Tv-res)
                                Tv-res)))]
          [(ref? ex) (let ([res (tenv-lkup env (ref->var ex))])
                       (add-type! (ref->lab ex) res)
                       res)]
          [(const? ex) (let* ([val (const->val ex)]
                              [lab (const->lab ex)]
                              [type (get-type val)])
                         (add-type! lab type)
                         type)]
          [(procedure? ex) 
           (cond [(equal? '+ ex) `(-> Int (-> Int Int))]
                 [else 'NYI])]
          [else (begin
                  (pretty-print `(unrecognized: ,ex))
                  'wtf)]))

  (list
    (T expr tenv)
    (tv-sub-all)
    (hash-table->alist tve)))



         )
