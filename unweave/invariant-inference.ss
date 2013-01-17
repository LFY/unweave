#!r6rs
(library (unweave invariant-inference)
         (export expr-search
                 find-subtype-constraints
                 infer-invariants)

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
                 (unweave external delimcc-simple-ikarus)

                 (unweave z3)

                 (unweave util)
                 
                 (unweave type-inference))

         (define (expr-search lab e)
           (define (found? l)
             (equal? lab l))
             (define (S e)
               (cond [(if? e) (explode-if e (lambda (l c t e)
                                              (if (found? l) (shift k (k e))
                                                (or (S c) (S t) (S e)))))]
                     [(lambda? e) (explode-lambda e (lambda (l vs c)
                                                      (if (found? l) 
                                                        (shift k (k e))
                                                        (or (fold (lambda (next acc)
                                                                    (or acc (S next)))
                                                                  #f
                                                                  vs)
                                                            (S c)))))]
                     [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                      (if (found? l)
                                                        (shift k (k e))
                                                        (or (fold (lambda (next-binding acc)
                                                                    (or acc (or (S (car next-binding))
                                                                                (S (cadr next-binding)))))
                                                                  #f
                                                                  bs)
                                                            (S c)))))]
                     [(call? e) (explode-call e (lambda (l f as)
                                                  (if (found? l)
                                                    (shift k (k e))
                                                    (or (S f) (fold (lambda (next acc)
                                                                      (or acc (S next)))
                                                                    #f
                                                                    as)))))]
                     [(ref? e) (if (found? (ref->lab e))
                                 (shift k (k e))
                                 #f)]
                     [(const? e) (explode-const e (lambda (l v)
                                                    (if (found? l)
                                                      (shift k (k e))
                                                      #f)))]
                     [else #f]))
             (reset (S e)))

         (define (find-subtype-constraints expr)
           (define subtype-constraints '())

           (define (add-subtype-constraint! l1 l2)
             (set! subtype-constraints (cons `(<: ,l1 ,l2)
                                             subtype-constraints)))

           (define (label-of ex)
             (cadr ex))

           (define (S e)
             (cond [(if? e) (explode-if e (lambda (l c t e)
                                            (add-subtype-constraint! (label-of t) l)
                                            (add-subtype-constraint! (label-of e) l)
                                            (S c)
                                            (S t)
                                            (S e)))]
                   [(lambda? e) (explode-lambda e (lambda (l vs c)
                                                    (S c)))]
                   [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                    (for-each (lambda (binding)
                                                                (S (cadr binding)))
                                                              bs)
                                                    (add-subtype-constraint! (label-of c) l)
                                                    (S c)))]
                   [(call? e) (explode-call e (lambda (l f as)
                                                (S f)
                                                (for-each (lambda (arg)
                                                            (S arg))
                                                          as)
                                                ))]
                   [(ref? e) '()]
                   [(const? e) '()]
                   [else 'err]))

           (begin (S expr)
                  subtype-constraints))

         ;; Searches for invariants over EXPR given the types stored in LABEL-TYPE-MAP
         ;; associating points in the program with Hindley-Milner types.
         ;; Uses the framework of Liquid Types (http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/about/)
         (define (infer-invariants expr label-type-map)

           (define subtype-constraints '())
           (define templates '())

           (define (add-subtype-constraint! l1 l2)
             (set! subtype-constraints (cons `(<: ,l1 ,l2)
                                             subtype-constraints)))

           (define (label-of ex)
             (cadr ex))

           (define lq-tvar-ctr 0)
           (define (next-lqtv!)
             (let* ([v (string->symbol (string-append "K" (number->string lq-tvar-ctr)))])
               (set! lq-tvar-ctr (+ 1 lq-tvar-ctr))
               v))

           (define (type->fresh-template! t)
             (cond [(primitive-type? t) `(: ,(next-lqtv!) ,t)]
                   [(arrow-type? t) `(-> ,(type->fresh-template! (arrow-type-arg t))
                                         ,(type->fresh-template! (arrow-type-res t)))]
                   [(parametric-type? t) `((: ,(next-lqtv!) ,(car t))
                                           ,@(map type->fresh-template! (cdr t)))]
                   [(type-variable? t) t] ;; preserve polymorphism
                   [else t]))

           (define (lab->fresh-template! lab)
             (let* ([hm-type (cdr (assoc lab label-type-map))])
               (type->fresh-template! hm-type)))

           (define (add-template! l)
             (let* ([template (lab->fresh-template! l)])
               (set! templates (cons (cons l template) templates))
               template))

           (define (I e)
             (cond [(if? e) (explode-if e (lambda (l c t e)
                                            (add-template! l)
                                            (add-subtype-constraint! (label-of t) l)
                                            (add-subtype-constraint! (label-of e) l)
                                            (I c)
                                            (I t)
                                            (I e)))]
                   [(lambda? e) (explode-lambda e (lambda (l vs c)
                                                    (add-template! l)
                                                    (I c)))]
                   [(letrec? e) (explode-letrec e (lambda (l bs c)
                                            (add-template! l)
                                                    (for-each (lambda (binding)
                                                                (I (cadr binding)))
                                                              bs)
                                                    (add-subtype-constraint! (label-of c) l)
                                                    (I c)))]
                   [(call? e) (explode-call e (lambda (l f as)
                                            (add-template! l)
                                                (I f)
                                                (for-each (lambda (arg)
                                                            (I arg))
                                                          as)
                                                ))]
                   [(ref? e) '()]
                   [(const? e) '()]
                   [else 'err]))
           (let* ([void (I expr)])
             `((subtype-constraints ,subtype-constraints)
               (templates ,templates))))
         )
