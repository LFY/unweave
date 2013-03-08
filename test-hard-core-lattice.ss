#!r6rs

(import (only (scheme-tools) pretty-print symbol-maker)
        (scheme-tools srfi-compat :69)
        (scheme-tools srfi-compat :1)
        (scheme-tools math)
        (scheme-tools bin)
        (unweave smt-search)
        (unweave external labeling)
        (unweave type-inference)
        (unweave invariant-inference))

(define expr2
  (quote (letrec ([list-map (lambda (f xs)
                              (if (null? xs) '()
                                (cons (f (car xs))
                                      (list-map f (cdr xs)))))]
                  [all (lambda (p xs) (if (null? xs) #t (and (p (car xs)) (all p (cdr xs)))))]
                  [conjunction (lambda (bs) (if (null? bs) #t (and (car bs) (conjunction (cdr bs)))))]
                  [consec2 (lambda (xs) (if (null? (cdr xs)) '()
                                          (cons (cons (car xs) (cons (car (cdr xs)) '()))
                                                (consec2 (cdr xs)))))]
                  [my-repeat (lambda (n f) (if (= 0 n) '() (cons (f) (my-repeat (- n 1) f))))]
                  [sample-site (lambda () (xrp 1 1 1 0 1))]
                  [grid (my-repeat 5 (lambda () (my-repeat 5 (lambda () (sample-site)))))]
                  [row-non-eq (lambda (row) (all (lambda (s1s2) (not (= (car s1s2) (car (cdr s1s2))))) (consec2 row)))]
                  [rows-noneq (lambda (gr) (all (lambda (row) (row-non-eq row)) gr))]
                  [cols-noneq (lambda (rows)
                                (if (null? (car rows)) 
                                  #t
                                  (and (row-non-eq (list-map (lambda (r) (car r)) rows))
                                       (letrec ([other-rows (list-map (lambda (c) (cdr c)) rows)])
                                         (cols-noneq other-rows)))))])
           (assert grid (lambda (g) (and (rows-noneq g) (cols-noneq g)))))))

(define transformed-expr (anf (label-transform expr2)))

(pretty-print transformed-expr)

(define inferred-types
  (infer-types transformed-expr
               `((+ . (-> Int (-> Int Int)))
                 (- . (-> Int (-> Int Int)))
                 (* . (-> Int (-> Int Int)))
                 (= . (-> Int (-> Int Bool)))
                 (and . (-> Bool (-> Bool Bool)))
                 (not . (-> Bool Bool))
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
                      (not . (-> (: (rf (V Bool) true) Bool x)
                                 (: (rf (V Bool) (= V (not x))) Bool ())))
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
