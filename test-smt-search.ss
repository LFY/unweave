#!r6rs

;; Test slice sampling

(import (only (scheme-tools) pretty-print symbol-maker)
        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)
        (scheme-tools math)
        (scheme-tools bin)
        (unweave smt-search))


;; XOR

(define (test-xor)
  (smt-mh-query
   100
   5
   '(letrec ([a (xrp flip-scorer flip flip-prop 0 1)]
             [b (xrp flip-scorer flip flip-prop 0 1)])
      (cons a (cons b '())))
   '(lambda (ab)
      (letrec ([a (car ab)]
               [b (car (cdr ab))])
        (= (+ (* a (- 1 b))
              (* (- 1 a) b))
           1))
      (-> (Lst Int) Bool))))


;; Open-universe Ising

(define (test-ising)
  (smt-mh-query
   100
   20
   '(letrec ([my-map (lambda (f xs)
                       (if (null? xs) '()
                           (cons (f (car xs))
                                 (my-map f (cdr xs))))
                       (-> (-> Int Int) (Lst (Lst Int)) (Lst Real)))]
             [sum-rand (lambda (k)
                         (if (= k 0) '()
                             (cons (xrp flip-scorer flip flip-prop 0 1)
                                   (sum-rand (- k 1))))
                         (-> Int (Lst Int)))]
             [consec2  (lambda (xs)
                         (if (null? (cdr xs)) '()
                             (cons (cons (car xs) (cons (car (cdr xs)) '()))
                                   (consec2 (cdr xs))))
                         (-> (Lst Int) (Lst (Lst Int))))]
             [eq (factor (x y) (if (= x y) 0.0 -0.6))]
             [xs (sum-rand (xrp flip-scorer flip flip-prop 4 5 6))]
             [constr (my-map (lambda (xy) (eq (car xy) (car (cdr xy))) (-> (Lst Int) Real))
                             (consec2 xs))])
      xs)
   '(lambda (xs) #t (-> (Lst Int) Bool))))


;; Generating sorted lists

(define (test-sorted-list)
  (smt-mh-query
   100
   20
   '(letrec ([sum-rand (lambda (k)
                         (if (= k 0) '()
                             (cons (xrp flip-scorer flip flip-prop 1 2 3 4)
                                   (sum-rand (- k 1))))
                         (-> Int (Lst Int)))]
             )
      (sum-rand (xrp flip-scorer flip flip-prop 4 5 6)))
   '(letrec ([increasing? (lambda (xs)
                            (if (null? (cdr xs)) #t
                                (if (> (car xs) (car (cdr xs))) #f
                                    (increasing? (cdr xs))))
                            (-> (Lst Int) Bool))])
      (lambda (xs) (and
               (> (car (cdr (cdr (cdr xs))))
                  (car (cdr (cdr xs))))
               (increasing? xs))
         (-> (Lst Int) Bool)))))


(define (main)
  (pretty-print (bin (test-xor)))
  (for-each pretty-print (test-ising))
  (for-each pretty-print (test-sorted-list)))


(main)
