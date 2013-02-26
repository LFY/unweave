;; Hindley-Milner type inference
;; From "Interpreting types as abstract values." (Oleg Kiselyov and Chung-chieh Shan) 
;; Formosan Summer School on Logic, Language, and Computation July 9–10, 2008.
;; URL: http://okmij.org/ftp/Computation/FLOLAC/lecture.pdf

#!r6rs
(library (unweave type-inference)
         (export infer-types
                 
                 type?
                 primitive-type?
                 type-variable?

                 arrow-type?
                 arrow-type-arg
                 arrow-type-res

                 parametric-type?
                 parametric-type-constructor
                 parametric-type-parameters

                 make-type-scheme
                 type-scheme?
                 type-scheme-vars
                 type-scheme-body
                 
                 make-TVE
                 unify
                 tv-chase
                 tv-sub)


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
        
;; (define (dpp x) '())

(define DEBUG #f)
(define (dpp x) 
  (if DEBUG (pretty-print x)))

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
       (member t '(Int Bool Real Lst unit))))

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

;; Type schemes
;; data TypS = TypS <instantiating-vars> Type

(define (make-type-scheme tvs type)
  `(ts ,tvs ,type))

(define (type-scheme? t)
  (and (pair? t) (equal? 'ts (car t))))

(define (type-scheme-vars ts)
  (cadr ts))

(define (type-scheme-body ts)
  (caddr ts))



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
  (cond [(arrow-type? type) `(-> ,(tv-sub tve (arrow-type-arg type)) 
                                 ,(tv-sub tve (arrow-type-res type)))]
        [(parametric-type? type)
         `(,(tv-sub tve (car type)) 
            ,@(map (lambda (t) (tv-sub tve t))
                   (cdr type)))]
        [(type-variable? type) (let* ([t (tv-lookup tve type)])
                                 (if (null? t) type
                                   (tv-sub tve t)))]
        
        [else type]))

(define (tv-chase tve type)
  (cond [(type-variable? type) (let* ([t (tv-lookup tve type)])
                                 (if (null? t) type
                                   (tv-chase tve t)))]
        [else type]))

;; Unification

(define (unify t1 t2 tve)
  (unify* (tv-chase tve t1) (tv-chase tve t2) tve))

(define (unify* t1 t2 tve)
  (dpp `(unify* ,t1 ,t2))
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
         (begin
           (dpp `(unify*-par-case ,t1 ,t2))
           (letrec ([loop (lambda (t1 t2 env)
                            (if (null? t1) env
                              (let ([res (unify (car t1) (car t2) env)])
                                (if (equal? 'MISMATCH res) res
                                  (loop (cdr t1) (cdr t2) res)))))])
             (loop (cdr t1) (cdr t2) tve)))]
        [(type-variable? t1) (unify-variables t1 t2 tve)]
        [(type-variable? t2) (unify-variables t2 t1 tve)]
        [else (begin
                (dpp `(mismatch ,t1 ,t2))
                'MISMATCH)]))

(define (unify-variables tvar type tve)
  (dpp `(unify-variables ,tvar ,type))
  (cond [(type-variable? type)
         (if (equal? type tvar)
           tve
           (begin (dpp `(unify-variables: unify ,tvar ,type))
           (tv-extend tve tvar type)))]
        [else (if (occurs tvar type tve)
                (begin
                  (dpp `(occurs-check ,tvar ,type ,(hash-table->alist tve)))
                  'OCCURS-CHECK)
                (begin
                  (dpp `(unify-variables: unify ,tvar ,type))
                (tv-extend tve tvar type)))]))

(define (occurs tvar type tve)
  (cond [(primitive-type? type) #f]
        [(arrow-type? type)
         (or (occurs tvar (arrow-type-arg type) tve)
             (occurs tvar (arrow-type-res type) tve))]
        [(parametric-type? type)
         (letrec ([loop (lambda (params)
                          (if (null? params) #f
                            (or (occurs tvar (car params) tve)
                                (loop (cdr params)))))])
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
 
  (define forbidden-free '())

  (define (preprocess-tenv tenv)
    (define (type-parameter? s)
      (and (symbol? s)
           (member (substring (symbol->string s) 0 1)
                   (map symbol->string '(a b c d e f g h i j k l m n o p q r s t u v w x y z)))))

    (define (walk-input-type t)
      (define unique-param-map '())
      (define (assign-param! x v)
        (set! unique-param-map (cons (cons x v) unique-param-map)))
      (define (W t)
        (cond [(primitive-type? t) t]
              [(arrow-type? t)
               `(-> ,(W (arrow-type-arg t))
                    ,(W (arrow-type-res t)))]
              [(parametric-type? t)
               `(,(W (car t)) ,@(map W (cdr t)))]
              [(type-parameter? t)
               (if (assoc t unique-param-map)
                 (cdr (assoc t unique-param-map))
                 (let* ([tvar (next-type-variable!)])
                   (assign-param! t tvar)
                   tvar))]
              [(null? t) 'unit]
              [else 'err]))
      (let* ([with-tvars (W t)])
        `(ts ,(map cdr unique-param-map)
             ,with-tvars)))

    (map (lambda (binding)
           (let* ([type (cdr binding)]
                  [ts (walk-input-type type)])
             (cons (car binding) ts)))
         tenv))

  (define tenv* (preprocess-tenv tenv))

  (define (next-type-variable!)
    (let* ([next-type-variable (string->symbol (string-append "T" (number->string type-variable-ctr)))])
      (set! type-variable-ctr (+ 1 type-variable-ctr))
      next-type-variable))

  (define (unify! t1 t2)
    (dpp `(unify ,t1 ,t2))
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
          [(boolean? v) 'Bool]
          [(null? v) `(Lst ,(next-type-variable!))]
          [else 'UNKNOWN]))

  ;; Type scheme instantiation
  (define (instantiate ts)

    (define (associate-with-freshvars tvs)
      (define (loop tvs)
        (if (null? tvs) '()
          (let* ([next-tve (loop (cdr tvs))]
                 [next-tv (next-type-variable!)])
            (dpp `(new-var ,(list (car tvs) next-tv type-variable-ctr)))
            (cons (cons (car tvs) next-tv)
                  next-tve))))
      (alist->hash-table (loop tvs)))

    (let* ([tve-tmp (associate-with-freshvars (type-scheme-vars ts))]
           [res (tv-sub tve-tmp (type-scheme-body ts))])
      (dpp `(instantiate ,ts ,res))
      res))

  ;; Generalization
  (define (generalize t-thunk)
    (define (freevars type)
      (dpp `(freevars ,type))
      (cond [(primitive-type? type) '()]
            [(parametric-type? type) (letrec ([loop (lambda (ts)
                                                      (if (null? ts) '()
                                                        (append (freevars (car ts))
                                                                (loop (cdr ts)))))])
                                       (loop type))]
            [(arrow-type? type) (append (freevars (arrow-type-arg type))
                                        (freevars (arrow-type-res type)))]
            [(type-variable? type) (list type)]
            [else '()]))

    (define (tv-dependent-set tve1 ctr1 tve2 ctr2)
      (define (num->tv-name i)
        (string->symbol 
          (string-append "T"
                         (number->string i))))

      (define (tvfree tve)
        (let* ([res
                 (filter (lambda (i)
                           (and
                             (not (hash-table-exists? tve i))
                             (not (member i forbidden-free))))
                (map num->tv-name (iota ctr1)))])
          (dpp `(tvfree ,res))
          res))

      (define (any f xs)
        (if (null? xs) #f
          (or (f (car xs)) (any f (cdr xs)))))
      (lambda (tv)
        (any (lambda (tvb)
               (dpp `(occurs ,tv ,tvb ,(occurs tv tvb tve2)))
               (occurs tv tvb tve2))
             (tvfree tve1))))

    (let* ([tve-before (hash-table->alist tve)]
           [ctr-before type-variable-ctr]
           [void (dpp `(tve-before ,tve-before ,ctr-before))]
           [t (t-thunk)]
           [void (dpp `(thunk-result ,t))]
           [tve-after (hash-table->alist tve)]
           [ctr-after type-variable-ctr]
           [void (dpp `(tve-after ,tve-after ,ctr-after))]
           [t* (tv-sub (alist->hash-table tve-after) t)]
           [tvdep (tv-dependent-set (alist->hash-table tve-before) ctr-before
                                    (alist->hash-table tve-after) ctr-after)]
           [void (dpp `(freevars t* ,(freevars t*)))]
           [fv (filter (lambda (x) (not (tvdep x)))
                       (delete-duplicates (freevars t*)))])
      (dpp `(tvdep-results ,(map (lambda (v) (cons v (tvdep v)))
                                          (delete-duplicates (freevars t*)))))
      (dpp `(final-generalized-type (ts ,fv ,t*)))
      `(ts ,fv ,t*)))

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
          [(factor? ex)
           (explode-factor ex (lambda (l vs call)
                                (T `(lambda ,l ,vs ,call) env)))]
          [(lambda? ex) 
           (explode-lambda ex (lambda (l vs call)
                                (dpp `(lam ,vs ,call ,env))
                                (let* ([new-tvars (map (lambda (v) 
                                                         (make-type-scheme 
                                                           '() 
                                                           (next-type-variable!))) 
                                                       vs)]
                                       [void (dpp `(env-after
                                                              ,(tenv-ext-multiple env
                                                                                 (map (lambda (v tv)
                                                                                        (cons v tv))
                                                                                      vs new-tvars))))]
                                       [Te (T call (tenv-ext-multiple env
                                                                      (map (lambda (v tv)
                                                                             (cons v tv))
                                                                           vs new-tvars)))]
                                       [final-type (if (null? vs)
                                                     `(-> unit ,Te)
                                                     (fold (lambda (next-type acc)
                                                           `(-> ,next-type ,acc))
                                                         Te
                                                         (map type-scheme-body (reverse new-tvars))))])
                                  
                                  (add-type! l final-type)
                                  final-type)))]
          [(assert? ex)
           (explode-assert ex (lambda (l prog constr)
                                (let* ([res-V (next-type-variable!)]
                                       [prog-type (T prog env)]
                                       [constr-type (T constr env)])
                                  (unify! res-V prog-type)
                                  (unify! `(-> ,res-V Bool) constr-type)
                                  (add-type! l `(-> ,res-V (-> ,constr-type ,res-V)))
                                  res-V)))]
          [(letrec? ex)
           (explode-letrec  ex (lambda (l bs call)
                                 (let* ([local-binding-env
                                          (fold (lambda (b e)
                                                  (let* ([Bv (next-type-variable!)]
                                                         [void (set! forbidden-free (cons Bv forbidden-free))]
                                                         [new-type (make-type-scheme '() Bv)]
                                                         [b-type (generalize (lambda () (T (cadr b) (tenv-ext e (car b) new-type))))])
                                                    (unify! Bv (type-scheme-body b-type))
                                                    (dpp `(adding-binding ,(car b)))
                                                    (dpp `(generalized: ,b-type))
                                                    (tenv-ext e (car b) b-type)))
                                                env bs)]
                                        [void (dpp 'letrec-after-bindings)]
                                        [void (dpp local-binding-env)]
                                        [final-type (T call local-binding-env)])
                                   (dpp 'got-final-type)
                                   (add-type! l final-type)
                                   final-type)))]
          [(call? ex)
           (explode-call ex (lambda (l f vs)
                              (dpp `(call ,l ,f ,vs ,env))
                              (let* ([Tf (T f env)]
                                     [Tvs (map (lambda (v) (T v env)) vs)]
                                     [Tv-res (next-type-variable!)]
                                     [function-type
                                       (fold (lambda (next-type acc)
                                               `(-> ,next-type ,acc))
                                             Tv-res
                                             (if (null? Tvs) 
                                               (list 'unit)
                                               (reverse Tvs)))])
                                (dpp `(func-type ,l ,function-type))
                                (unify! Tf function-type)
                                (add-type! l Tv-res)
                                Tv-res)))]
          [(ref? ex) (let ([res (instantiate (tenv-lkup env (ref->var ex)))])
                       (add-type! (ref->lab ex) res)
                       res)]
          [(xrp? ex) (explode-xrp ex (lambda (lab scorer name prop-fx-name params)
                                       (let* ([types (map (lambda (p) (T p env)) params)])
                                         (add-type! lab (car types))
                                         (car types))))]
          [(const? ex) (let* ([val (const->val ex)]
                              [lab (const->lab ex)]
                              [type (get-type val)])
                         (add-type! lab type)
                         type)]
          [(procedure? ex) 
           (cond [(equal? '+ ex) `(-> Int (-> Int Int))]
                 [else 'NYI])]
          [else (begin
                  (dpp `(unrecognized: ,ex))
                  'wtf)]))

  (list
    (tv-sub tve (T expr tenv*))
    (tv-sub-all)
    (hash-table->alist tve))))
