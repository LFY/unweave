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
     (letrec ([list-map (lambda (f xs)
                          (if (null? xs) '()
                            (cons (f (car xs))
                                  (list-map f (cdr xs)))))]
              [random-list (lambda ()
                             (if (xrp 1 1 1 #t #f) '()
                               (cons (xrp 1 1 1 2 3)
                                     (random-list))))])
       (list-map (lambda (x) 
                   (letrec ([smp (xrp 1 1 1 0 1)])
                     (+ x smp)))
                 (random-list)))
     (lambda (xs) 
       (letrec ([sum-list 
                  (lambda (xs)
                    (if (null? xs) 0
                      (+ (car xs) 
                         (sum-list (cdr xs)))))])
         (and (= (car xs) (car (cdr xs)))
              (< (sum-list xs) 10))))))
              
(define transformed-expr (anf (label-transform expr2)))

(pretty-print transformed-expr)

(define inferred-types
  (infer-types transformed-expr
               `((+ . (-> Int (-> Int Int)))
                 (- . (-> Int (-> Int Int)))
                 (* . (-> Int (-> Int Int)))
                 (= . (-> Int (-> Int Bool)))
                 (and . (-> Bool (-> Bool Bool)))
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

                      (and . (-> (: (rf (V Bool) true) Bool x)
                                 (-> (: (rf (V Bool) true) Bool y)
                                     (: (rf (V Bool) (= V (and x y))) Bool ()))))
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

(pretty-print (smt-calc-prob 20 transformed-expr (cadr inferred-types) label->invariant-map))
