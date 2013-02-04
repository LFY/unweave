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

           (define (shallow-call? expr)
             (and (call? expr)
                  (let* ([args (explode-call expr (lambda (l f as)
                                                    as))])
                    (all (lambda (a) 
                           (and (not (call? a))
                                (not (lambda? a))
                                (not (letrec? a))))
                         args))))

           (define (N e) e)

           (define (A e)
             (cond [(lambda? e) (explode-lambda e (lambda (l vs call)
                                                    `(lambda ,l ,vs ,(reset (A call)))))]
                   [(if? e) (explode-if e (lambda (l c t e)
                                            (let* ([cv (next-var!)])
                                              (reset 
                                                `(letrec ,(next-lab!)
                                                   ([,cv ,(A c)])
                                                   (if ,(next-lab!) (ref ,(next-lab!) ,cv)
                                                     ,(A t)
                                                     ,(A e)))))))]
                   [(call? e) (explode-call e (lambda (l f as)
                                                (if (null? as) e
                                                  (let* ([new-f-var (if (ref? f) '() (next-var!))]
                                                         [new-vars (map (lambda (x) 
                                                                          (if (or (ref? x)
                                                                                  (const? x))
                                                                            '()
                                                                            (next-var!))) 
                                                                        as)]
                                                         [res-var (next-var!)])
                                                    (shift k
                                                           `(letrec ,(next-lab!)
                                                              ,(append (if (null? new-f-var) '() (list (list new-f-var (A f))))
                                                                       (filter (lambda (x) (not (null? x)))
                                                                               (map (lambda (v x) (if (null? v)
                                                                                                    '() (list v (A x)))) new-vars as))

                                                                       (list `(,res-var
                                                                                (call ,(next-lab!)
                                                                                      ,(if (null? new-f-var) f
                                                                                         `(ref ,(next-lab!)
                                                                                               ,new-f-var))
                                                                                      ,@(map (lambda (v a)
                                                                                               (if (null? v) a
                                                                                                 `(ref ,(next-lab!) ,v)))
                                                                                             new-vars as))
                                                                                ))
                                                                       )
                                                              ,(k `(ref ,(next-lab!) ,res-var))
                                                              ))))))]
                   [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                    (reset 
                                                      `(letrec ,(next-lab!)
                                                         ,(map (lambda (b)
                                                                 `(,(car b) ,(if (shallow-call? (cadr b))
                                                                               (N (cadr b))
                                                                               (A (cadr b)))))
                                                               bs)
                                                         ,(if (shallow-call? c)
                                                            (N c)
                                                            (A c))))))]
                   [else e]))

           (let* ([answer (reset (A expr))])
             answer))

         ;; data Template = (: Refinement ActualType CorrespondingVar) | Template -> Template
         ;; data Refinement = LiquidTypeVariable Sym | (rf (V Type) <formula>)

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

           (define lqtvs '())
           (define lq-tvar-ctr 0)
           (define (next-lqtv!)
             (let* ([v (string->symbol (string-append "K" (number->string lq-tvar-ctr)))])
               (set! lq-tvar-ctr (+ 1 lq-tvar-ctr))
               (set! lqtvs (cons v lqtvs))
               v))

           (define (type->fresh-template! t)
             (cond [(primitive-type? t) `(: ,(next-lqtv!) ,t ())]
                   [(arrow-type? t) `(-> ,(type->fresh-template! (arrow-type-arg t))
                                         ,(type->fresh-template! (arrow-type-res t)))]
                   [(parametric-type? t) `(,(car t)
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

           (define (add-variables vs template)
             (define (loop vs current)
               (if (null? vs) current
                 `(-> ,(let* ([t (arrow-type-arg current)])
                         (if (template? t)
                           `(: ,(cadr t) ,(caddr t) ,(car vs))
                           `(: ,(next-lqtv!) ,t ,(car vs))))
                      ,(loop (cdr vs) (arrow-type-res current)))))
             (loop vs template))

           (define (extract-vars args f-constr)
             (if (null? args) '()
               (cons (cadddr (arrow-type-arg f-constr))
                     (extract-vars (cdr args)
                                   (arrow-type-res f-constr)))))

           (define (I e env)
             (cond [(if? e) (explode-if e (lambda (l c t e)
                                            (let* ([template (get-template! l)]
                                                   [c-constr (I c env)]
                                                   [then-condition (ext (next-ectv!) c env)]
                                                   [else-condition (ext (next-ectv!) `(call a666 (ref a666 not) ,c) env)]
                                                   [t-constr (I t then-condition)]
                                                   [e-constr (I e else-condition)]
                                                   [res (cons template (append (ret->constr c-constr)
                                                                               (ret->constr t-constr)
                                                                               (ret->constr e-constr)
                                                                               (list
                                                                                 (env-constr env template)
                                                                                 (env-constr then-condition 
                                                                                             `(<: ,(ret->template t-constr) ,template))
                                                                                 (env-constr else-condition 
                                                                                             `(<: ,(ret->template e-constr) ,template)))))])
                                              res)))]
                   [(lambda? e) (explode-lambda e (lambda (l vs c)
                                                    (let* ([template (get-template! l)]
                                                           [vs* (if (null? vs) '(())
                                                                  vs)]
                                                           [template+vars (add-variables vs* template)]
                                                           [var+arg-types (letrec ([loop (lambda (vars-left curr-arrow-type)
                                                                                           (if (null? vars-left) '()
                                                                                             (cons (cons (car vars-left) 
                                                                                                         (arrow-type-arg curr-arrow-type))
                                                                                                   (loop (cdr vars-left) 
                                                                                                         (arrow-type-res curr-arrow-type)))))])
                                                                            (loop vs* template+vars))]
                                                           [next-env (fold (lambda (var-type curr-env)
                                                                             (ext (car var-type)
                                                                                  (cdr var-type)
                                                                                  curr-env))
                                                                           env
                                                                           var+arg-types)])
                                                      (let* ([c-constr (I c next-env)])
                                                        (cons template+vars (append (ret->constr c-constr)
                                                                                    (list (env-constr env template+vars)
                                                                                          (env-constr next-env `(<: ,(ret->template c-constr)
                                                                                                                    ,(fold (lambda (next acc)
                                                                                                                             (arrow-type-res acc))
                                                                                                                           template+vars
                                                                                                                           vs*))))))))))]
                   [(letrec? e) (explode-letrec e (lambda (l bs c)
                                                    (let* ([template (get-template! l)]
                                                           [other-constraints '()]
                                                           [local-binding-env
                                                             (fold (lambda (next-binding curr-env)
                                                                     (let* ([placeholder-template 
                                                                              (get-template! (cadr (cadr next-binding)))]
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
                                                      (cons template (append other-constraints c-constraints
                                                                             (list (env-constr local-binding-env template)
                                                                                   (env-constr local-binding-env `(<: ,c-template ,template))))))))]
                   [(call? e) (explode-call e (lambda (l f as)
                                                (let* ([template (get-template! l)]
                                                       [f-constr (I f env)]
                                                       [f-template (ret->template f-constr)]
                                                       [f-res-type (fold (lambda (next acc)
                                                                           (arrow-type-res acc))
                                                                         f-template
                                                                         (if (null? as)
                                                                           (cons '() as)
                                                                           as))]
                                                       [args-constrs (map (lambda (a) (I a env)) as)])
                                                  (cons `(substitute ,(map (lambda (v x)
                                                                             `(,v ,x))
                                                                           (extract-vars as f-template)
                                                                           as)
                                                                     ,f-res-type)
                                                        (append (ret->constr f-constr)
                                                                (apply append (map cdr args-constrs))
                                                                )))))]
                   [(ref? e) (let* ([template (get-template! (ref->lab e))])
                               (if (primitive-type? (unwrap-template template))
                                 (cons `(rf (V ,(caddr template))
                                            (and (== V ,(ref->var e)))) '())
                                 (cons (lkup (ref->var e) env) '())))]
                   [(const? e) (let* ([template (get-template! (cadr e))])
                                 (cond [(number? (const->val e))
                                        (cons `(rf (V Int) (and (= V ,(const->val e)))) '())]
                                       [else (cons template '())]))]
                   [else 'err]))
           (let* ([template+constraints (I expr env)]
                  [initial-sol (make-initial-substitution expr label-type-map (split-constraints (cdr template+constraints)))]
                  [void (pretty-print initial-sol)]
                  [initial-lift (lift-invariants initial-sol)])
             `((templates ,templates)
               (variables ,lqtvs)
               (final ,template+constraints)
               (initial-sub ,initial-sol)
               (lifted ,initial-lift))))

         ;; Templates
         
         (define (template? t)
           (and (pair? t)
                (equal? ': (car t))))

         (define (refinement? t)
           (and (pair? t)
                (equal? 'rf (car t))))

         (define (subtype? t)
           (and (pair? t)
                (equal? '<: (car t))))

         (define (template-variable? t)
           (and (symbol? t)
                (equal? "K" (substring (symbol->string t) 0 1))))

         (define (substitution? t)
           (and (pair? t)
                (equal? 'substitute (car t))))


         (define (split-constraints constraints)
           (define (split-function-template t)
             (define (loop curr acc)
               (cond [(arrow-type? curr)
                      (loop (arrow-type-res curr) 
                            (let* ([arg-refinement (arrow-type-arg curr)]
                                   [variable (cadddr arg-refinement)]
                                   [final-binding (cons variable arg-refinement)])
                              (cons final-binding acc)))]
                     [else `(,(reverse acc) ,curr)]))
             (loop t '()))
           (define (split-constraint c)
             (define extra-bindings '())
             (define (add-binding! b)
               (set! extra-bindings (cons b extra-bindings)))
             (define (S c)
               (cond [(arrow-type? c) (let* ([env+split-constr (split-function-template c)]
                                             [final-constr (cadr env+split-constr)]
                                             [bindings (car env+split-constr)])
                                        (for-each add-binding! bindings)
                                        final-constr)]
                     [(subtype? c) `(<: ,(S (cadr c))
                                        ,(S (caddr c)))]
                     [else c]))
             (let* ([env (cadr c)]
                    [transformed-constr (S (caddr c))])
               (list
                 '=>
                 (append extra-bindings env)
                 transformed-constr)))

           (map split-constraint constraints))

         (define (make-initial-substitution expr label-type-map constraints)

           (define var-type-map
             (filter (lambda (x) (not (null? x)))
                     (map (lambda (l-t)
                            (let* ([l (car l-t)]
                                   [type (cdr l-t)]
                                   [my-subexpr (expr-search l expr)])
                              (if (ref? my-subexpr)
                                (cons (ref->var my-subexpr)
                                      type)
                                '())))
                          label-type-map)))

           (define (possible-primitive-predicates variables)
             (define operators '(< > <= >=))
             (define constants '(0))

             (define (c-product . xss)
               (define (loop acc xs)
                 (if (null? xs)
                   (list (reverse acc))
                   (apply append
                          (map (lambda (x)
                                 (loop (cons x acc)
                                       (cdr xs)))
                               (car xs)))))
               (loop '() xss))

             (define (all-pairs xs)
               (cond [(null? xs) '()]
                     [else
                       (append (map (lambda (y)
                                      (list (car xs) y))
                                    xs)
                               (all-pairs (cdr xs)))]))

             (define (over-all-operators pairs)
               (apply append (map (lambda (p)
                                    (map (lambda (o)
                                           `(,o ,(car p) ,(cadr p)))
                                         operators))
                                  pairs)))
             (append (over-all-operators (c-product constants variables))
                     (over-all-operators 
                       (filter (lambda (xy)
                                 (not (equal? (car xy) (cadr xy))))
                               (all-pairs variables)))))

           (define (process-one-constraint c)
             (define (make-formula env)
               (let* ([variables (map car env)])
                 (pretty-print `(variables ,variables))
                 (pretty-print `(var-type-map ,var-type-map))
                 (pretty-print `(filtered-variables ,(filter (lambda (v) (and (assoc v var-type-map)
                                                                              (equal? 'Int (cdr (assoc v var-type-map))))) 
                                                             variables)))
                 (possible-primitive-predicates (cons 'V (filter (lambda (v) (and (assoc v var-type-map)
                                                                                  (equal? 'Int (cdr (assoc v var-type-map))))) 
                                                                 variables)))))
             (define (get-variables constr)
               (define (loop c)
                 (cond [(refinement? c) '()]
                       [(subtype? c) (append (get-variables (cadr c))
                                             (get-variables (caddr c)))]
                       [(template? c) (if (and (template-variable? (cadr c))
                                               (equal? 'Int (caddr c)))
                                        (list (cons (cadr c)
                                                    (caddr c)))
                                        '())]
                       [(arrow-type? c) (append (get-variables (arrow-type-arg c))
                                                (get-variables (arrow-type-res c)))]
                       [else '()]))
               (delete-duplicates (loop constr)))
             (let* ([env (cadr c)]
                    [constr (caddr c)])
               (map (lambda (v) 
                      (cons v (make-formula env)))
                    (get-variables constr))))

           (let* ([environments (map cadr constraints)]
                  [orig-constraints (map caddr constraints)]
                  [assignments (map process-one-constraint constraints)])
             (zip environments
                  orig-constraints
                  assignments)))

         (define (lift-invariants sub)
           (define all-assignments
             (apply append (map caddr sub)))
           (define all-constraints
             (map cadr sub))
           (define all-environments
             (map car sub))
           (define (lookup-var v)
             (let* ([lookup-res (assoc `(,v . Int) all-assignments)])
               (if lookup-res lookup-res
                 `((,v . Int)))))

           (define (search-and-replace bindings body)
             (define (TRE expr)
               (cond [(pair? expr)
                      (cons (TRE (car expr))
                            (TRE (cdr expr)))]
                     [(symbol? expr)
                      (if (not (assoc expr bindings)) expr
                        (cdr (assoc expr bindings)))]
                     [else expr]))

             (define (TR expr)
               (cond [(arrow-type? expr)
                      `(-> ,(TR (arrow-type-arg expr))
                           ,(TR (arrow-type-res expr)))]
                     [(template? expr)
                      `(: ,(TR (cadr expr))
                          ,(caddr expr)
                          ,(cadddr expr))]
                     [(refinement? expr)
                      `(rf ,(cadr expr)
                           (and ,@(let* ([old-conjunction (cdr (caddr expr))]
                                         [new-conjunction (map TR old-conjunction)])
                                    new-conjunction)))]
                     [else expr]))
             (TR body))

           (define (L t)
             (cond [(subtype? t)
                    `(<: ,(L (cadr t))
                         ,(L (caddr t)))]
                   [(arrow-type? t)
                    `(-> ,(L (arrow-type-arg t))
                         ,(L (arrow-type-res t)))]
                   [(template? t)
                    (let ([t* (cadr t)]
                          [assoc-var (cadddr t)])
                      `(: ,(cond  [(refinement? t*) t*]
                                  [(and (template-variable? t*) 
                                        (equal? 'Int (caddr t)))
                                   (let* ([lookup-result (lookup-var t*)]
                                          [var-name-type (car lookup-result)]
                                          [var-type (cdr var-name-type)])
                                     `(rf (V ,var-type)
                                          (and ,@(cdr lookup-result))))]
                                  [else t*])
                          ,(caddr t)
                          ,(cadddr t)))]
                   [(substitution? t)
                    (let* ([body (L (caddr t))]
                           [bindings (cadr t)])
                      (search-and-replace
                        bindings
                        body))]
                   [else t]))

           (zip (map (lambda (env)
                       (map (lambda (var-val)
                              (pretty-print `(solve ,(car var-val) ,(cdr var-val)))
                              `(,(car var-val) . ,(L (cdr var-val))))
                            env))
                     all-environments)
                (map L all-constraints)))

         )