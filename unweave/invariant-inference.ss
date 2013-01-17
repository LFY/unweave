#!r6rs
(library (unweave invariant-inference)
         (export expr-search
                 infer-invariants
                 anf)
         (import (rnrs)
                 (rnrs eval)
                 (only (ikarus) set-car!)

                 (only (scheme-tools) pretty-print symbol-maker)

                 (scheme-tools srfi-compat :69)
                 (scheme-tools srfi-compat :1)

                 (scheme-tools math)

                 (unweave external normal-interpreter)
                 (unweave external labeling)
                 (unweave external church-syntax)
                 (unweave external delimcc-simple-ikarus)

                 (unweave z3)

                 (unweave util)
                 
                 (unweave type-inference))

         (define (anf expr)
           (define lab-ctr 0)
           (define (next-lab!)
             (let* ([v (string->symbol (string-append "l" (number->string var-ctr)))])
               (set! var-ctr (+ 1 var-ctr))
               v))

           (define var-ctr 0)
           (define (next-var!)
             (let* ([v (string->symbol (string-append "x" (number->string var-ctr)))])
               (set! var-ctr (+ 1 var-ctr))
               v))
           (define (A e)
             (cond [(lambda? e) (explode-lambda e (lambda (l vs call)
                                                    `(lambda ,l ,vs ,(A call))))]
                   [(if? e) (explode-if e (lambda (l c t e)
                                            (let* ([cv (next-var!)])
                                              `(letrec ,(next-lab!)
                                                 ([,cv ,(A c)])
                                                 (if ,(next-lab!) (ref ,(next-lab!) ,cv)
                                                   ,(A t)
                                                   ,(A e))))))]
                   [(call? e) (explode-call e (lambda (l f as)
                                                (if (null? as) e
                                                  (let* ([new-f-var (if (ref? f) '() (next-var!))]
                                                         [new-vars (map (lambda (x) 
                                                                          (if (or (ref? x)
                                                                                  (const? x))
                                                                            '()
                                                                            (next-var!))) 
                                                                        as)])
                                                    `(letrec ,(next-lab!)
                                                       ,(append (if (null? new-f-var) '() (list (list new-f-var (A f))))
                                                                (filter (lambda (x) (not (null? x)))
                                                                        (map (lambda (v x) (if (null? v)
                                                                                             '() (list v (A x)))) new-vars as)))
                                                       (call ,(next-lab!)
                                                             ,(if (null? new-f-var) f
                                                                `(ref ,(next-lab!)
                                                                      ,new-f-var))
                                                             ,@(map (lambda (v a)
                                                                      (if (null? v) a
                                                                        `(ref ,(next-lab!) ,v)))
                                                                    new-vars as)))))))]
                   [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                    `(letrec ,(next-lab!)
                                                       ,(map (lambda (b)
                                                               `(,(car b) ,(A (cadr b))))
                                                             bs)
                                                       ,(A c))))]
                   [else e]))

           (let* ([answer (A expr)])
             answer))

         (define (unwrap-template t)
           (cond [(and (pair? t) (equal? ': (car t)))
                  (unwrap-template (caddr t))]
                 [else t]))

         (define (expr-search lab e)
           (define (found? l)
             (equal? lab l))
             (define (S e)
               (cond [(if? e) (explode-if e (lambda (l c t e)
                                              (if (found? l) (shift k (k e))
                                                (or (S c) (S t) (S e)))))]
                     [(lambda? e) (explode-lambda e (lambda (l vs c)
                                                      (if (found? l) 
                                                        (shift k (k e))
                                                        (or (fold (lambda (next acc)
                                                                    (or acc (S next)))
                                                                  #f
                                                                  vs)
                                                            (S c)))))]
                     [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                      (if (found? l)
                                                        (shift k (k e))
                                                        (or (fold (lambda (next-binding acc)
                                                                    (or acc (or (S (car next-binding))
                                                                                (S (cadr next-binding)))))
                                                                  #f
                                                                  bs)
                                                            (S c)))))]
                     [(call? e) (explode-call e (lambda (l f as)
                                                  (if (found? l)
                                                    (shift k (k e))
                                                    (or (S f) (fold (lambda (next acc)
                                                                      (or acc (S next)))
                                                                    #f
                                                                    as)))))]
                     [(ref? e) (if (found? (ref->lab e))
                                 (shift k (k e))
                                 #f)]
                     [(const? e) (explode-const e (lambda (l v)
                                                    (if (found? l)
                                                      (shift k (k e))
                                                      #f)))]
                     [else #f]))
             (reset (S e)))

         ;; Searches for invariants over EXPR given the types stored in LABEL-TYPE-MAP
         ;; associating points in the program with Hindley-Milner types.
         ;; Uses the framework of Liquid Types (http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/about/)
         (define (infer-invariants expr label-type-map env)

           (define subtype-constraints '())
           (define templates '())
           

           (define (add-subtype-constraint! l1 l2)
             (set! subtype-constraints (cons `(<: ,l1 ,l2)
                                             subtype-constraints)))

           (define (label-of ex)
             (cadr ex))

           (define lq-tvar-ctr 0)
           (define (next-lqtv!)
             (let* ([v (string->symbol (string-append "K" (number->string lq-tvar-ctr)))])
               (set! lq-tvar-ctr (+ 1 lq-tvar-ctr))
               v))

           (define (type->fresh-template! t)
             (cond [(primitive-type? t) `(: ,(next-lqtv!) ,t)]
                   [(arrow-type? t) `(-> ,(type->fresh-template! (arrow-type-arg t))
                                         ,(type->fresh-template! (arrow-type-res t)))]
                   [(parametric-type? t) `((: ,(next-lqtv!) ,(car t))
                                           ,@(map type->fresh-template! (cdr t)))]
                   [(type-variable? t) t] ;; preserve polymorphism
                   [else t]))

           (define (lab->fresh-template! lab)
             (let* ([hm-type (cdr (assoc lab label-type-map))])
               (type->fresh-template! hm-type)))

           (define (get-template! l)
             (if (not (assoc l templates))
               (let* ([template (lab->fresh-template! l)])
                 (set! templates (cons (cons l template) templates))
                 template)
               (cdr (assoc l templates))))

           (define (lkup v env)
             (let* ([res (assoc v env)])
               (if (equal? #f res)
                 'not-found
                 (cdr res))))

           (define (ext var val env)
             (cons (cons var val) env))

           (define (I-ret template constraints)
             (cons template constraints))

           (define ret->constr cdr)
           (define ret->template car)

           (define expr-constr-ctr 0)
           (define (next-ectv!)
             (let* ([v (string->symbol (string-append "E" (number->string expr-constr-ctr)))])
               (set! expr-constr-ctr (+ 1 expr-constr-ctr))
               v))

           (define (env-constr env template)
             `(=> ,env ,template))

           ;; TODO:
           ;; 0. A-normal-form conversion
           ;; 1. How to associate program variables in the type?
           ;; (-> (: K1 T4 x) ...) ?

           (define (I e env)
             (cond [(if? e) (explode-if e (lambda (l c t e)
                                            (let* ([template (get-template! l)]
                                                   [c-constr (I c env)]
                                                   [t-constr (I t env)]
                                                   [e-constr (I e env)])
                                              (cons template (append (ret->constr c-constr)
                                                                     (ret->constr t-constr)
                                                                     (ret->constr e-constr)
                                                                     (list
                                                                       (env-constr env template)
                                                                       (env-constr (ext (next-ectv!) t env) 
                                                                                   `(<: ,(ret->template t-constr) ,template))
                                                                       (env-constr (ext (next-ectv!) `(call a666 (ref a666 not) ,t) env) 
                                                                                   `(<: ,(ret->template e-constr) ,template))))))))]
                   [(lambda? e) (explode-lambda e (lambda (l vs c)
                                                    (let* ([template (get-template! l)]
                                                           [vs* (if (null? vs) '(())
                                                                  vs)]
                                                           [var+arg-types (letrec ([loop (lambda (vars-left curr-arrow-type)
                                                                                           (if (null? vars-left) '()
                                                                                           (cons (cons (car vars-left) 
                                                                                                       (arrow-type-arg curr-arrow-type))
                                                                                                 (loop (cdr vars-left) 
                                                                                                       (arrow-type-res curr-arrow-type)))))])
                                                                            (loop vs* template))]
                                                           [next-env (fold (lambda (var-type curr-env)
                                                                             (ext (car var-type)
                                                                                  (cdr var-type)
                                                                                  curr-env))
                                                                           env
                                                                           var+arg-types)])
                                                      (let* ([c-constr (I c next-env)])
                                                        (cons template (append (ret->constr c-constr)
                                                                               (list (env-constr env template)
                                                                                     (env-constr next-env `(<: ,(ret->constr c-constr)
                                                                                                               ,(arrow-type-res template))))))))))]
                   [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                    (let* ([template (get-template! l)]
                                                           [other-constraints '()]
                                                           [local-binding-env
                                                             (fold (lambda (next-binding curr-env)
                                                                     (let* ([placeholder-template 
                                                                              `(: ,(next-lqtv!) ,(get-template! (cadr (cadr next-binding))))]
                                                                            [next (I (cadr next-binding)
                                                                                     (ext (car next-binding)
                                                                                          placeholder-template
                                                                                          curr-env))])
                                                                       (set! other-constraints (append (ret->constr next) other-constraints))
                                                                       (ext (car next-binding) (ret->template next) curr-env)))
                                                                   env
                                                                   bs)]
                                                           [c-constr (I c local-binding-env)]
                                                           [c-template (ret->template c-constr)]
                                                           [c-constraints (ret->constr c-constr)])
                                                      (cons template (append other-constraints
                                                                             (list (env-constr env template)
                                                                                   (env-constr env `(<: ,c-template ,template))))))))]
                   [(call? e) (explode-call e (lambda (l f as)
                                                (let* ([template (get-template! l)]
                                                       [f-constr (I f env)]
                                                       [args-constrs (map (lambda (a) (I a env)) as)])

                                                  (cons `(sub ,f ,as ,template)
                                                        (append (ret->constr f-constr)
                                                                (apply append (map cdr args-constrs))
                                                                )))))]
                   [(ref? e) (let* ([template (get-template! (ref->lab e))])
                               (if (primitive-type? (unwrap-template template))
                                 (cons `(== V ,(ref->var e)) '())
                                 (cons (lkup (ref->var e) env) '())))]
                   [(const? e) (let* ([template (get-template! (cadr e))])
                                 (cons template '()))]
                   [else 'err]))
           (let* ([template+constraints (I expr env)])
             `((templates ,templates)
               (final ,template+constraints))))
         )
