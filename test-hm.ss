(import (unweave type-inference)
        (unweave external labeling)
        (only (scheme-tools) pretty-print))


(define labeled2 (label-transform
                   `(letrec ([map (lambda (f xs)
                                    (if (null? xs) '()
                                      (cons (f (car xs))
                                            (map f (cdr xs)))))])
                      map)))
                      ;; (letrec ([termid (lambda (x) x)])
                      ;;   (map (lambda (x) (+ x 1))
                      ;;        (cons 1 (cons 2 '())))))))

                      ;; (lambda (f)
                      ;;   (lambda (y)
                      ;;     (+ (car (map (lambda (x) (+ x 1))
                      ;;                  (cons 1 (cons 2 '()))))
                      ;;        ((termid f) (+ (termid y) 1))))))))


(pretty-print labeled2)
(pretty-print (infer-types labeled2 `((+ . (-> Int (-> Int Int)))
                                      (cons . (-> a (-> (Lst a) (Lst a))))
                                      (car . (-> (Lst a) a))
                                      (cdr . (-> (Lst a) (Lst a)))
                                      (null? . (-> (Lst a) Bool)))))

;; (define termid '(lambda (x) x))

;; (define labeled2 (label-transform
;;                    `(lambda (f)
;;                       (lambda (y)
;;                         ((,termid f) (+ (,termid y) 1))))))

;; (pretty-print labeled2)
;; (pretty-print (infer-types labeled2 `((+ . (-> Int (-> Int Int))))))
