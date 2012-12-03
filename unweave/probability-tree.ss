#!r6rs

(library

 (unweave probability-tree)

 (export pv?
         pv->dist
         dist
         reify
         pv-ret
         pv-concat
         pv-prob
         contains-atom?
         pv-unfold
         pv-unfold-by)

 (import (rnrs)
         (unweave external delimcc-simple-ikarus))


 ;; dist, reify, etc.

 (define (every-other xs)
   (if (null? xs) '()
       (cons (list (car xs) (cadr xs))
             (every-other (cddr xs)))))

 (define (pv? e)
   (and (list? e) (not (null? e)) (equal? 'pv (car e))))

 (define pv->dist cdr)

 (define (dist . vp-args)
   (let* ([pvs (map (lambda (vp) `(,(cadr vp) ,(car vp)))
                    (every-other vp-args))])
     (shift k `(pv ,@(map (lambda (pv)
                            `(,(car pv) ;; Probability
                              ,(lambda () (k (cadr pv))) ;; Continuation
                              ,(cadr pv))) ;; Sampled value
                          pvs)))))

 (define (reify thunk)
   (reset (thunk)))

 ;; are pv nodes used to define choice points?

 (define (pv-ret v)
   `(pv ,(list 1.0 v v)))

 (define (pv-concat pvs)
   `(pv ,@(apply append (map pv->dist pvs))))

 (define (pv-prob p pv)
   `(pv ,@(map (lambda (pvs)
                 `(,(* p (car pvs))
                   ,(cadr pvs)
                   ,(caddr pvs)))
               (pv->dist pv))))

 (define (contains-atom? a e)
   (cond [(pair? e)
          (or (contains-atom? a (car e))
              (contains-atom? a (cdr e)))]
         [else (equal? a e)]))

 ;; (end Hansei duplication)


 ;; Enhance search tree with partial traces
 ;; (pv (probability continuation-thunk sample-value
 ;;      (trace-expr ...
 ;;         <thunk> ;; recursion
 ;;         (pv ... ;; another choice following in control flow

 ;; (define (pv-unfold2 pv-tree)
 ;;   (define (unfold-trace v)
 ;;     (cond [(null? v) '()]
 ;;           [(procedure? v) (reify (lambda () (v)))]
 ;;           [(pair? v) (cond [(equal? 'continue (car v))
 ;;                             (let* ([call (cadr v)]
 ;;                                    [proc (caddr v)])
 ;;                               `(,call ,(proc))]
 ;;                             [else `(,(unfold-trace (car v)) .

 (define (pv-unfold pv-tree)
   (define (unfold-trace v)
     (cond [(null? v) '()]
           [(procedure? v) (reify (lambda () (v)))]
           [(pair? v) `(,(unfold-trace (car v)) . ,(unfold-trace (cdr v)))]
           [else v]))
   (define (unfold-atom pv)
     `(pv (,(car pv) ,(cadr pv) ,(caddr pv)
           ,(let* ([val (cadr pv)]
                   [smp (caddr pv)]
                   [prob (car pv)]
                   [unexpanded (null? (cdddr pv))])
              (if unexpanded
                  (cond [(procedure? val)
                         (let* ([res (val)]) (if (pv? res) (pv-prob prob res) res))]
                        [(pair? val) (unfold-trace val)]
                        [else val])
                  (pv-unfold (cadddr pv)))))))
   (cond
    [(pv? pv-tree) (let* ([choices (pv->dist pv-tree)]) (pv-concat (map unfold-atom choices)))]
    [(procedure? pv-tree) (reset (pv-tree))]
    [(pair? pv-tree) `(,(pv-unfold (car pv-tree)) . ,(pv-unfold (cdr pv-tree)))]
    [else pv-tree]))

 (define (pv-unfold-by n pv-tree)
   (if (= n 0) pv-tree
       (let* ([next-tree (pv-unfold pv-tree)])
         (pv-unfold-by (- n 1) next-tree))))

 )
