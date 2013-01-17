(import (unweave type-inference)
        (unweave invariant-inference)
        (unweave external labeling)
        (only (scheme-tools) pretty-print))



(define expr (label-transform
                   `(letrec ([geometric (lambda ()
                                          (if (flip)
                                            0
                                            (+ 1 (geometric))))])
                      (geometric))))
                      ;; (letrec ([termid (lambda (x) x)])
                      ;;   (map (lambda (x) (+ x 1))
                      ;;        (cons 1 (cons 2 '())))))))

                      ;; (lambda (f)
                      ;;   (lambda (y)
                      ;;     (+ (car (map (lambda (x) (+ x 1))
                      ;;                  (cons 1 (cons 2 '()))))
                      ;;        ((termid f) (+ (termid y) 1))))))))


(define types (infer-types expr `((+ . (-> Int (-> Int Int)))
                                      (cons . (-> a (-> (Lst a) (Lst a))))
                                      (car . (-> (Lst a) a))
                                      (cdr . (-> (Lst a) (Lst a)))
                                      (null? . (-> (Lst a) Bool))
                                      (flip . (-> () Bool)))))

(define label-type-map (cadr types))

(pretty-print expr)

(pretty-print (infer-invariants expr label-type-map '()))

;; 
;; (define termid '(lambda (x) x))

;; (define expr (label-transform
;;                    `(lambda (f)
;;                       (lambda (y)
;;                         ((,termid f) (+ (,termid y) 1))))))

;; (pretty-print expr)
;; (pretty-print (infer-types expr `((+ . (-> Int (-> Int Int))))))
