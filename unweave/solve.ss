#!r6rs

;; Constraint solving algorithm: incremental unfolding

;; step 1. unfold model
;; step 2. collect assignments that satisfy the constraints (expressed as query stmt on the resulting sample)
;; step 3. add those assignments to the store
;; step 4. goto 1, but add that assignment to the set of forbidden states.

(library

 (unweave solve)

 (export incremental-unfold)

 (import (rnrs)
         (unweave probability-tree)
         (unweave z3)
         (unweave formula)
         (only (scheme-tools) pretty-print))

 (define (incremental-unfold query tree max-depth)
   (define models '())
   (define (loop depth curr-tree)
     (if (= depth max-depth) 'done
         (let* ([formula (unfolded-tree->formula curr-tree)]
                [model (run-z3 (append formula
                                       (list `(assert ,(query 'Y0))
                                             '(check-sat)
                                             '(get-model))))])
           (pretty-print 'tree-and-formula)
           (pretty-print curr-tree)
           (pretty-print formula)

           (if (equal? 'sat (car model))
               (begin
                 (set! models (cons model models))
                 (loop (+ 1 depth) (pv-unfold (pv-unfold curr-tree))))
               (begin
                 (set! models (cons 'unsat models))
                 (loop (+ 1 depth) (pv-unfold (pv-unfold curr-tree))))))))
   (pretty-print tree)
   (loop 0 (pv-unfold tree))
   models)

 )