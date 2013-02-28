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
     (letrec ([geometric (lambda ()
                           (if (xrp 1 1 1 #t #f)
                             '() 
                             (if (xrp 1 1 1 #t #f)
                               (cons 1 (geometric))
                               (cons 1 (cons 1 (geometric))))))])
       (geometric))
     (lambda (n) (equal? n 
                         (cons 1 (cons 1 (cons 1 (cons 1 '()))))))))

(define transformed-expr
  (anf (label-transform expr2)))

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

;; (define inferred-invariants
;;   (infer-invariants transformed-expr (cadr inferred-types)
;;                     '((unit . (: (rf (V unit) true) unit ()))
;;                       (flip . (-> () (: (rf (V Bool) (or (= true V) (= false V))) Bool ())))
;;                       (+ . (-> (: (rf (V Int) true) Int x)
;;                                (-> (: (rf (V Int) true) Int y)
;;                                    (: (rf (V Int) (= V (+ x y))) Int ()))))
;;                       (- . (-> (: (rf (V Int) true) Int x)
;;                                (-> (: (rf (V Int) true) Int y)
;;                                    (: (rf (V Int) (= V (- x y))) Int ()))))
;;                       (* . (-> (: (rf (V Int) true) Int x)
;;                                (-> (: (rf (V Int) true) Int y)
;;                                    (: (rf (V Int) (= V (* x y))) Int ()))))
;;                       (= . (-> (: (rf (V Int) true) Int x)
;;                                (-> (: (rf (V Int) true) Int y)
;;                                    (: (rf (V Bool) (= V (= x y))) Bool ()))))
;;                       (> . (-> (: (rf (V Int) true) Int x)
;;                                (-> (: (rf (V Int) true) Int y)
;;                                    (: (rf (V Bool) (= V (> x y))) Bool ()))))
;;                       (< . (-> (: (rf (V Int) true) Int x)
;;                                (-> (: (rf (V Int) true) Int y)
;;                                    (: (rf (V Bool) (= V (< x y))) Bool ())))))))

;; (pretty-print inferred-invariants)

;; (define label->invariant-map (caddr inferred-invariants))

(define label->invariant-map '())

(pretty-print (smt-calc-prob 100 transformed-expr (cadr inferred-types) label->invariant-map))
