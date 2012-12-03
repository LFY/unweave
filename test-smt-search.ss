#!r6rs

(import (only (scheme-tools) pretty-print symbol-maker)
        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)
        (scheme-tools math)
        (unweave smt-search))

;; Prints 'unknown' after unfolding 8 times.
(pretty-print 'unknown-test)
(pretty-print (smt-solve 8
                         '(letrec ([geometric (lambda ()
                                                (if (xrp flip-scorer flip flip-prop #t #f)
                                                  0
                                                  (+ 1 (geometric))) (-> () Int))])
                            (geometric))
                         '(lambda (n) (< n 0))))

;; returns a satisfying assignment for (> (geometric) 3)
(pretty-print 'lt3-test)
(pretty-print (smt-solve 8
                         '(letrec ([geometric (lambda ()
                                                (if (xrp flip-scorer flip flip-prop #t #f)
                                                  0
                                                  (+ 1 (geometric))) (-> () Int))])
                            (geometric))
                         '(lambda (n) (< n 3))))

;; returns a satisfying assignment
(pretty-print 'eq5-test)
(pretty-print (smt-solve 8
                         '(letrec ([geometric (lambda ()
                                                (if (xrp flip-scorer flip flip-prop #t #f)
                                                    0
                                                    (+ 1 (geometric))) (() Int))])
                            (geometric))
                         '(lambda (n) (= n 5))))

;; returns a satisfying assignment
(pretty-print 'nonrec-eq4-test)
(pretty-print (smt-solve 8
                         '(letrec ([x1 (xrp flip-scorer flip flip-prop -1 0 1)]
                                   [x2 (if (> x1 0)
                                         (xrp flip-scorer flip flip-prop -2 2)
                                         (xrp flip-scorer flip flip-prop -4 4))])
                            (+ x1 x2))
                         '(lambda (n) (= n 4))))

;; lists
(pretty-print 'random-list-test)
(pretty-print (smt-solve 8
                         '(letrec ([sum-rand (lambda (k)
                                               (if (= k 0) '()
                                                 (cons (xrp flip-scorer flip flip-prop -1 0 1 2 3)
                                                       (sum-rand (- k 1))))
                                               (-> Int (Lst Int)))]
                                   [increasing? (lambda (xs)
                                                  (if (null? (cdr xs)) #t
                                                    (if (> (car xs) (car (cdr xs))) #f
                                                      (increasing? (cdr xs))))
                                                  (-> (Lst Int) Bool))])
                            (increasing? (sum-rand 3)))
                         '(lambda (x) x (-> Bool Bool))))
