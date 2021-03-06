#!r6rs

(library

 (unweave tests)

 (export run-tests)

 (import (rnrs)
         (unweave probability-tree)
         (unweave formula)
         (unweave random-primitives)
         (unweave solve)
         (only (scheme-tools) system pretty-print format))

 (define (geometric-gen)
   (if (dist #t 0.5 #f 0.5)
       0
       `(+ 1 ,(lambda () (geometric-gen)))))

 (define (model)
   (if (dist #t 0.5 #f 0.5)
       (lambda () (f))
       (dist 3 0.5 4 0.5)))

 (define (f)
   (dist 1 0.5 2 0.5))

 (define (g)
   (dist 3 0.5 4 0.5))

 (define (run-tests)

   (define initial-tree (reify (lambda () (geometric-gen))))

   ;; we need an odd number here?

   (define test-query (lambda (result)
                        `(= ,result 10)))

   ;; (pretty-print (run-z3 (append test-formula (list '(check-sat) '(get-model)))))

   ;; 2. hook up query statements properly (Y0 == Result)

   ;; Introducing query/constraint statements
   ;; query: just an SMT 2.0 assert formula on the return value

   (pretty-print initial-tree)
   (pretty-print (pv-unfold initial-tree))
   (pretty-print (unfolded-tree->formula (pv-unfold initial-tree)))
   (pretty-print (pv-unfold (pv-unfold initial-tree)))
   ;; (for-each pretty-print (incremental-unfold test-query initial-tree 10)))
   )
 )
