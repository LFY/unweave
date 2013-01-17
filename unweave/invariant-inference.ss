#!r6rs
(library (unweave invariant-inference)
         (export expr-search
                 find-subtype-constraints)

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

         (define (infer-invariants expr label-type-map)
           '())
         )
