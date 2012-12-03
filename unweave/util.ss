#!r6rs

(library

 (unweave util)

 (export set-list-elt!
         init
         some all
         randint
         uniform-select)

 (import (rnrs)
         (only (ikarus) set-car!)
         (unweave random-primitives))

 (define (set-list-elt! lst elt n)
   (let loop ([curr lst]
              [i 0])
     (if (= i n)
         (set-car! curr elt)
         (loop (cdr curr) (+ i 1)))))

 (define (init xs)
   (if (null? (cdr xs)) '()
       (cons (car xs) (init (cdr xs)))))

 (define (some p xs)
   (if (null? xs) #f
       (or (p (car xs)) (some p (cdr xs)))))

 (define (all p xs)
   (if (null? xs) #t
       (and (p (car xs)) (all p (cdr xs)))))

 (define (randint a b)
   (+ a (random-integer (+ 1 (- b a)))))

 (define (uniform-select xs)
   (list-ref xs (randint 0 (- (length xs) 1))))

 )