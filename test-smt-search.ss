(import (only (scheme-tools) pretty-print symbol-maker)

        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)

        (scheme-tools math)

        (unweave smt-search))

(pretty-print (smt-solve 8
       '(letrec ([geometric (lambda ()
                              (if (xrp flip-scorer flip flip-prop #t #f)
                                0
                                (+ 1 (geometric))) (() Int))])
          (geometric))
       '(lambda (n) (< n 0))))

