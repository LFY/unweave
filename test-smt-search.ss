#!r6rs

(import (only (scheme-tools) pretty-print symbol-maker)
        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)
        (scheme-tools math)
        (unweave smt-search))
(import (printing)
        (unweave smt-search))

;; block proposals on sorted lists
(for-each pretty-print
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
                              (= 3 (car (cdr (cdr xs))))
                              (increasing? xs))
                 (-> (Lst Int) Bool)))))
