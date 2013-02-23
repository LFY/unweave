(import (unweave type-inference)
        (unweave invariant-inference)
        (unweave external labeling)
        (only (scheme-tools) pretty-print))

;; (define expr (label-transform
;;                `(letrec ([id (lambda (x) x)])
;;                   (id (lambda (x) (id (+ x 1)))))))
(define expr (anf (label-transform
               `(letrec ([geometric (lambda ()
                                      (if (flip) 0 
                                        (letrec ([x (geometric)])
                                          (+ 1 x))))])
                  (geometric)))))
;; (define expr (anf (label-transform
;;                     `(letrec ([geometric (lambda ()
;;                                            (if (flip) 0 (+ 1 (geometric))))])
;;                        (geometric)))))

;; (define expr (anf (label-transform
;;                    `(letrec ([max (lambda (x y)
;;                                     (if (> x y) 
;;                                       x y))])
;;                       max))))


(define types (infer-types expr `((+ . (-> Int (-> Int Int)))
                                  (- . (-> Int (-> Int Int)))
                                  (* . (-> Int (-> Int Int)))
                                  (= . (-> Int (-> Int Bool)))
                                  (> . (-> Int (-> Int Bool)))
                                  (cons . (-> a (-> (Lst a) (Lst a))))
                                  (car . (-> (Lst a) a))
                                  (cdr . (-> (Lst a) (Lst a)))
                                  (null? . (-> (Lst a) Bool))
                                  (flip . (-> () Bool)))))

(pretty-print expr)
(pretty-print types)

(define label-type-map (cadr types))


(pretty-print (infer-invariants expr label-type-map '((unit . (: (rf (V unit) true) unit ()))
                                                      (flip . (-> () (: (rf (V Bool) (or (= true V) (= false V))) Bool ())))
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
                                                                   (: (rf (V Bool) (= V (== x y))) Bool ()))))
                                                      (> . (-> (: (rf (V Int) true) Int x)
                                                               (-> (: (rf (V Int) true) Int y)
                                                                   (: (rf (V Bool) (= V (> x y))) Bool ())))))))


