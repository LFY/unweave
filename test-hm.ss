(import (unweave type-inference)
        (unweave invariant-inference)
        (unweave external labeling)
        (only (scheme-tools) pretty-print))



(define expr (anf (label-transform
                   `(letrec ([max (lambda (x y)
                                    (if (> x y) x y))])
                      (max 3 4)))))

(pretty-print expr)

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

(pretty-print types)

(define label-type-map (cadr types))


(pretty-print (infer-invariants expr label-type-map '((flip . (-> () (: (rf (V Bool) (or (= true V) (= false V))))))
                                                      (+ . (-> (: (rf (V Int) ()) Int x)
                                                               (-> (: (rf (V Int) ()) Int y)
                                                                   (: (rf (V Int) (= V (+ x y))) Int ()))))
                                                      (- . (-> (: (rf (V Int) ()) Int x)
                                                               (-> (: (rf (V Int) ()) Int y)
                                                                   (: (rf (V Int) (= V (- x y))) Int ()))))
                                                      (* . (-> (: (rf (V Int) ()) Int x)
                                                               (-> (: (rf (V Int) ()) Int y)
                                                                   (: (rf (V Int) (= V (* x y))) Int ()))))
                                                      (= . (-> (: (rf (V Int) ()) Int x)
                                                               (-> (: (rf (V Int) ()) Int y)
                                                                   (: (rf (V Bool) (= V (== x y))) Bool ()))))
                                                      (> . (-> (: (rf (V Int) ()) Int x)
                                                               (-> (: (rf (V Int) ()) Int y)
                                                                   (: (rf (V Bool) (= V (> x y))) Bool ()))))
                                                      )))


