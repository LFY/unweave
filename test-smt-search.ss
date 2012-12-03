#!r6rs

(import (only (scheme-tools) pretty-print symbol-maker)
        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)
        (scheme-tools math)
        (unweave smt-search))

;; Prints 'unknown' after unfolding 8 times.
(pretty-print (smt-solve 8
                         '(letrec ([geometric (lambda ()
                                                (if (xrp flip-scorer flip flip-prop #t #f)
                                                    0
                                                    (+ 1 (geometric))) (() Int))])
                            (geometric))
                         '(lambda (n) (< n 0))))

;; returns a satisfying assignment for (> (geometric) 3)
(pretty-print (smt-solve 8
                         '(letrec ([geometric (lambda ()
                                                (if (xrp flip-scorer flip flip-prop #t #f)
                                                    0
                                                    (+ 1 (geometric))) (() Int))])
                            (geometric))
                         '(lambda (n) (< n 3))))

;; returns a satisfying assignment
(pretty-print (smt-solve 8
                         '(letrec ([geometric (lambda ()
                                                (if (xrp flip-scorer flip flip-prop #t #f)
                                                    0
                                                    (+ 1 (geometric))) (() Int))])
                            (geometric))
                         '(lambda (n) (= n 5))))

;; returns a satisfying assignment
(pretty-print (smt-solve 8
                         '(letrec ([x1 (xrp flip-scorer flip flip-prop -1 0 1)]
                                   [x2 (if (> x1 0)
                                           (xrp flip-scorer flip flip-prop -2 2)
                                           (xrp flip-scorer flip flip-prop -4 4))])
                            (+ x1 x2))
                         '(lambda (n) (= n 4))))
