#!r6rs

;; Test slice sampling

(import (only (scheme-tools) pretty-print symbol-maker)
        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)
        (scheme-tools math)
        (scheme-tools bin)
        (unweave smt-search)
        (unweave external labeling)
        (unweave type-inference)
        (unweave invariant-inference))


;; Geometric

(define expr2
  '(assert
     (letrec ([list-map (lambda (f xs2)
                          (if (null? xs2) '()
                            (cons (f (car xs2))
                                  (list-map f (cdr xs2)))))]
              [sum-list (lambda (xs)
                          (if (null? xs) 0
                            (+ (car xs) 
                               (sum-list (cdr xs)))))])
       (sum-list (list-map (lambda (x) (+ x 1)) 
                           (cons (xrp 1 1 1 1 2 3 4)
                                 (cons (xrp 1 1 1 1 2 3 4)
                                       (cons (xrp 1 1 1 1 2 3 4) 
                                             '()))))))
     (lambda (n) (< n 10))))
              
(define transformed-expr (anf (label-transform expr2)))

(pretty-print transformed-expr)

(define inferred-types
  (infer-types transformed-expr
               `((+ . (-> Int (-> Int Int)))
                 (- . (-> Int (-> Int Int)))
                 (* . (-> Int (-> Int Int)))
                 (= . (-> Int (-> Int Bool)))
                 (equal? . (-> a (-> a Bool)))
                 (> . (-> Int (-> Int Bool)))
                 (< . (-> Int (-> Int Bool)))
                 (cons . (-> a (-> (Lst a) (Lst a))))
                 (() . (Lst a))
                 (car . (-> (Lst a) a))
                 (cdr . (-> (Lst a) (Lst a)))
                 (null? . (-> (Lst a) Bool))
                 (flip . (-> () Bool)))))

(pretty-print transformed-expr)
(pretty-print inferred-types)

(define inferred-invariants
  (infer-invariants transformed-expr (cadr inferred-types)
                    '((unit . (: (rf (V unit) true) unit ()))
                      (flip . (-> () (: (rf (V Bool) (or (= true V) (= false V))) Bool ())))
                      (car . (-> (: (rf (V (Lst a)) true) (Lst a) xs) (: (rf (V a) (= V (car xs))) a ())))
                      (cdr . (-> (: (rf (V (Lst a)) true) (Lst a) xs) (: (rf (V (Lst a)) (= V (cdr xs))) (Lst a) ())))
                      (null? . (-> (: (rf (V (Lst a)) true) (Lst a) x)
                                   (: (rf (V Bool) (= V (= nil x))) Bool ())))

                      (cons . (-> (: (rf (V a) true) a x)
                                  (-> (: (rf (V (Lst a)) true) (Lst a) y)
                                      (: (rf (V (Lst a)) (= V (cons x y))) (Lst a) ()))))
                      (equal? . (-> (: (rf (V a) true) a x)
                                    (-> (: (rf (V a) true) a y)
                                        (: (rf (V Bool) (= V (= x y))) Bool ()))))
                      (() . (: (rf (V (Lst a)) true) (Lst a) ()))
                      (+ . (-> (: (rf (V Int) true) Int x)
                               (-> (: (rf (V Int) true) Int y)
                                   (: (rf (V Int) (= V (+ x y))) Int ()))))
                      (- . (-> (: (rf (V Int) true) Int x)
                               (-> (: (rf (V Int) true) Int y)
                                   (: (rf (V Int) (= V (- x y))) Int ()))))
                      (* . (-> (: (rf (V Int) true) Int x)
                               (-> (: (rf (V Int) true) Int y)
                                   (: (rf (V Int) (= V (* x y))) Int ()))))
                      (= . (-> (: (rf (V Int) true) Int x)
                               (-> (: (rf (V Int) true) Int y)
                                   (: (rf (V Bool) (= V (= x y))) Bool ()))))
                      (> . (-> (: (rf (V Int) true) Int x)
                               (-> (: (rf (V Int) true) Int y)
                                   (: (rf (V Bool) (= V (> x y))) Bool ()))))
                      (< . (-> (: (rf (V Int) true) Int x)
                               (-> (: (rf (V Int) true) Int y)
                                   (: (rf (V Bool) (= V (< x y))) Bool ())))))))

(pretty-print inferred-invariants)

(define label->invariant-map (caddr inferred-invariants))

(pretty-print (smt-calc-prob 100 transformed-expr (cadr inferred-types) '()))
