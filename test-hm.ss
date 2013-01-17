(import (unweave type-inference)
        (unweave invariant-inference)
        (unweave external labeling)
        (only (scheme-tools) pretty-print))



(define expr (anf (label-transform
                   `(letrec ([geometric (lambda ()
                                          (if (flip)
                                            0
                                            (+ 1 (geometric))))])
                      (geometric)))))

(pretty-print expr)

(define types (infer-types expr `((+ . (-> Int (-> Int Int)))
                                      (cons . (-> a (-> (Lst a) (Lst a))))
                                      (car . (-> (Lst a) a))
                                      (cdr . (-> (Lst a) (Lst a)))
                                      (null? . (-> (Lst a) Bool))
                                      (flip . (-> () Bool)))))

(define label-type-map (cadr types))


(pretty-print (infer-invariants expr label-type-map '((flip . (-> () (rf (V Bool) (or (= true V)
                                                                                      (= false V))))))))


