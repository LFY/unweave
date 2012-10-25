#!r6rs

(library

 (unweave random-primitives)

 (export rnd-select)

 (import (rnrs)
         (srfi :27)
         (scheme-tools srfi-compat :1))

 (define (uniform a b)
   (+ a (* (- b a) (random-real))))

 (define (randint a b)
   (+ (random-integer (+ (- b a) 1)) a))

 (define (scan f z xs)
   (cond [(null? xs) `(,z)]
         [else (let* ([res (f z (car xs))])
                 (cons z (scan f res (cdr xs))))]))

 (define (scan1 f xs)
   (scan f (car xs) (cdr xs)))

 (define (rnd-select pvs)
   (cond [(null? pvs) '()]
         [else
          (letrec* ([smp (uniform 0 1)]
                    [pvs* (zip (scan1 + (map car pvs)) pvs)]
                    [iterator (lambda (pvs)
                                (let* ([pv (car pvs)]
                                       [p (car pv)]
                                       [v (cadr pv)])
                                  (cond [(< smp p) v]
                                        [else (iterator (cdr pvs))])))])
                   (iterator pvs*))]))

 (random-source-randomize! default-random-source)

 )