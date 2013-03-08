#!r6rs
(library (unweave invariant-inference)
         (export expr-search
                 search-and-replace
                 infer-invariants
                 let-split
                 anf
                 template?)
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

         (define (let-split expr)
           (define lab-ctr 0)
           (define (next-lab!)
             (let* ([v (string->symbol (string-append "s" (number->string lab-ctr)))])
               (set! lab-ctr (+ 1 lab-ctr))
               v))
           (cond [(letrec? expr)
                  (explode-letrec expr (lambda (l bs c)
                                         (if (null? (cdr bs))
                                           `(letrec ,(next-lab!) ,bs ,c)
                                           `(letrec ,(next-lab!) ,(list (car bs))
                                              ,(let-split
                                                 `(letrec (next-lab!) ,(cdr bs) ,c))))))]
                 [(lambda? expr)
                  (explode-lambda expr (lambda (l vs c)
                                         `(lambda ,l ,vs ,(let-split c))))]
                 [(if? expr)
                  (explode-if expr (lambda (l c t e)
                                     `(if ,l ,(let-split c) ,(let-split t) ,(let-split e))))]
                 [(call? expr)
                  (explode-call expr (lambda (l f as)
                                       `(call ,l ,(let-split f) ,@(map let-split as))))]
                 [else expr]))

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
                                                `(letrec ,(next-lab!)
                                                   ([,cv ,(A c)])
                                                   (if ,(next-lab!) (ref ,(next-lab!) ,cv)
                                                     ,(reset (A t))
                                                     ,(reset (A e)))))))]
                   [(assert? e) (explode-assert e (lambda (l prog constr) (reset (reset `(assert ,l ,(A prog) ,(A constr))))))]
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
                                                    `(letrec ,(next-lab!)
                                                       ,(map (lambda (b)
                                                               `(,(car b) ,(if (shallow-call? (cadr b))
                                                                             (N (cadr b))
                                                                             (reset (A (cadr b))))))
                                                             bs)
                                                       ,(if (shallow-call? c)
                                                          (N c)
                                                          (reset (A c))))))]
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
                   [(assert? e) (explode-assert e (lambda (l prog c)
                                                    (if (found? l)
                                                      (shift k (k e))
                                                      (or (S prog) (S c)))))]
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

           (define (search-and-replace bindings body)
             (define (TRE expr)
               (cond [(pair? expr)
                      (cons (TRE (car expr))
                            (TRE (cdr expr)))]
                     [(symbol? expr)
                      (if (not (assoc expr bindings)) 
                        expr
                        (cdr (assoc expr bindings)))]
                     [else expr]))
             (TRE body))

             (define (polymorphic? t)
               (cond [(type-variable? t) #t]
                     [(primitive-type? t) #f]
                     [(arrow-type? t)
                      (or (polymorphic? (arrow-type-arg t))
                          (polymorphic? (arrow-type-res t)))]
                     [(parametric-type? t)
                      (some polymorphic? (cdr t))]
                     [else #f]))
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
                   [(parametric-type? t) (if (polymorphic? t) t
                                           `(: ,(next-lqtv!) ,t ()))]
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
                 (begin
                   (pretty-print `(err-not-found ,v))
                   'not-found)
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
               (if (not (template? (arrow-type-arg f-constr)))
                 (cons '() (extract-vars (cdr args)
                               (arrow-type-res f-constr)))
                 (cons (cadddr (arrow-type-arg f-constr))
                       (extract-vars (cdr args)
                                     (arrow-type-res f-constr))))))

           (define (restrict specific general)
             (define (remove-templates t)
               (cond [(template? t) (caddr t)]
                     [(arrow-type? t) `(-> ,(remove-templates (arrow-type-arg t)) ,(remove-templates (arrow-type-res t)))]
                     [(parametric-type? t) `(,(car t) ,@(map remove-templates (cdr t)))]
                     [(substitution? t) (remove-templates (caddr t))]
                     [else t]))
             (define (replace-template t new-type)
               (cond [(template? t) `(: ,(replace-template (cadr t) new-type) ,new-type ,(cadddr t))]
                     [(refinement? t) `(rf ,(let* ([old (cadr t)]
                                                   [new `(,(car old) ,new-type)])
                                              new)
                                           ,@(cddr t))]
                     [else t]))
             (define (get-type-of t)
               (cond [(template? t) (caddr t)]
                     [(refinement? t) (cadr (cadr t))]
                     [else t]))
             (let* ([t1* (remove-templates specific)]
                    [t2* (get-type-of general)]
                    ;; [void (pretty-print `(t1* ,t1* t2* ,t2*))]
                    [t1p (search-and-replace '((a . T666)) t1*)]
                    [t2p (search-and-replace '((a . T667)) t2*)]
                    [final (tv-sub (unify t1p t2p (make-TVE)) t1p)])
               ;; (pretty-print `(final: ,final))
               (replace-template general final)))


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
                   [(or
                      (lambda? e)
                      (factor? e))
                    (explode-lambda e (lambda (l vs c)
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

                   [(assert? e) (explode-assert e (lambda (l prog constr) (I prog env)))]
                   ;; [(assert? e) (explode-assert e (lambda (l prog constr) (I `(call ,l ,constr ,prog) env)))]
                                                    ;; (let* ([pct (I prog env)] 
                                                    ;;        [cct (I constr env)]
                                                    ;;        [c-template (ret->template cct)]
                                                    ;;        [c-template* (if (template? c-template) (caddr c-template) c-template)]
                                                    ;;        [c-res-template (arrow-type-res c-template*)]
                                                    ;;        [sub-constr 
                                                    ;;          `(substitute ,(map (lambda (v x) `(,v ,(de-label x '()))) 
                                                    ;;                             (extract-vars (list prog) c-template*) (list prog)) 
                                                    ;;                       ,c-res-template)])
                                                    ;;   (cons (car pct)
                                                    ;;         (append 
                                                    ;;                 (cdr pct)
                                                    ;;                 (cdr cct))))))]
                                                    ;; (I `(call ,l ,constr ,prog) env)))]
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
                                                       [f-template* (if (template? f-template)
                                                                             (caddr f-template) 
                                                                             f-template)]
                                                       [f-res-type (fold (lambda (next acc)
                                                                           (arrow-type-res acc))
                                                                         f-template*
                                                                         (if (null? as)
                                                                           (cons '() as)
                                                                           as))]
                                                       [args-constrs (map (lambda (a) (I a env)) as)]
                                                       ;; [void (pretty-print `(restrict ,l ,as ,f-template* ,template ,f-res-type))]
                                                       [f-res-type* (restrict template f-res-type)])
                                                  ;; template: the type after substituting all type variables (may contain more...), and contains the new template variable
                                                  ;; f-res-type: may be polymorphic but may contain more specific information about the type
                                                  ;; we would like to constraint the type of f-res-type to be template, to make it no more general than template
                                                  ;; step 1. if f-res-type is a refinement, 
                                                  (cons `(substitute ,(map (lambda (v x)
                                                                             `(,v ,x))
                                                                           (extract-vars as f-template*)
                                                                           as)
                                                                     ,f-res-type*)
                                                        (append (ret->constr f-constr)
                                                                (apply append (map cdr args-constrs))
                                                                )))))]
                   [(ref? e) (let* ([template (get-template! (ref->lab e))])
                               (if (primitive-type? (unwrap-template template))
                                 (cons `(rf (V ,(caddr template))
                                            (and (= V ,(ref->var e)))) '())
                                 (cons (lkup (ref->var e) env) '())))]
                   [(xrp? e) (explode-xrp e (lambda (lab scorer name prop-fx-name params)
                                               (let* ([template (get-template! lab)]
                                                      [param-templates+constrs (map (lambda (p) (I p env)) params)]
                                                      [final-forms (map (lambda (p) (de-label p '())) params)]
                                                      [to-add (apply append (map cdr param-templates+constrs))])
                                                 ;; (pretty-print `(final-forms ,final-forms))
                                                 (cons `(rf (V ,(caddr template))
                                                            (or ,@(map (lambda (f)
                                                                         `(= V ,(if (boolean? f)
                                                                                  (if f 'true 'false)
                                                                                  f)))
                                                                       final-forms)))
                                                       to-add))))]
                   [(const? e) (let* ([template (get-template! (cadr e))])
                                 (cond [(number? (const->val e))
                                        (cons `(rf (V Int) (and (= V ,(const->val e)))) '())]
                                       [else (cons template '())]))]
                   [else 'err]))
           (let* ([template+constraints (I expr env)]
                  [splitted (split-constraints (cdr template+constraints))]
                  ;; [void (pretty-print `(templates ,templates))]
                  ;; [void (pretty-print `(splitted ,splitted))]
                  [constraint-types (get-constraint-types splitted)]
                  [splitted* (map car (filter (lambda (c-t) (not (polymorphic? (cadr c-t))))
                                              (zip splitted constraint-types)))]
                  [constraint-types* (filter (lambda (t) (not (polymorphic? t))) constraint-types)]
                  ;; [void (pretty-print `(get-constraint-types ,constraint-types))]
                  [responsible-variables (get-responsible-variables splitted*)]
                  [var-type-map (label->var-type-map expr label-type-map)]
                  ;; [void (pretty-print `(vtm ,label-type-map ,var-type-map))]
                  [initial-sol (make-initial-substitution expr label-type-map splitted* constraint-types*)]
                  [initial-asn (to-assignment initial-sol)]
                  [solution (solve initial-asn initial-sol var-type-map constraint-types* responsible-variables)])
             `(solution
                ,solution
                ,(make-invariant-annotations (alist->hash-table solution)
                                             templates))))

         (define (make-invariant-annotations assignment templates)
           (define (annotate template)
             (cond [(arrow-type? template)
                    `(-> ,(annotate (arrow-type-arg template))
                         ,(annotate (arrow-type-res template)))]
                   [(parametric-type? template)
                    `(,(car template) ,@(map annotate (cdr template)))]
                   [(template? template)
                    `(: ,(annotate (cadr template))
                        ,@(cddr template))]
                   [(template-variable? template)
                    `(and ,@(let* ([lookup-res (hash-table-ref assignment template (lambda () '(true)))])
                              (if (null? lookup-res)
                                'true
                                lookup-res)))]
                   [else template]))
           (map (lambda (x)
                  (cons (car x)
                        (annotate (cdr x))))
                templates))

         (define (solve initial-asn initial-sol var-type-map constraint-types responsible-variables)
           (define (all p xs)
             (if (null? xs) #t
               (and (p (car xs))
                    (all p (cdr xs)))))

           (define (first-index-of p xs)
             (define (loop k xs)
               (if (null? xs) #f
                 (if (p (car xs)) k
                   (loop (+ k 1) (cdr xs)))))
             (loop 0 xs))

           (define (stop-at p xs) (if (null? xs) '() (if (p (car xs)) (car xs) (stop-at p (cdr xs)))))

           (define (unsat? e) (and (pair? e) (equal? 'unsat (car e))))
           (define valid? unsat?)

           (define (re-project new-asn) (map run-z3 (map make-smt-prog (lift-invariants2 new-asn initial-sol var-type-map constraint-types))))
           (define (re-project-single c t new-asn)
             (let* ([lifted (car (lift-invariants2 new-asn 
                                                   (list c) 
                                                   var-type-map 
                                                   (list t)))]
                    [to-compute (make-smt-prog lifted)])
               (run-z3 to-compute)))
           (define (weaken asn v qualifiers raw-constr raw-constr-type)
             (define (good? candidate)
               (hash-table-set! asn v candidate)
               (let* ([res (re-project-single raw-constr raw-constr-type asn)])
                 (valid? res)))
             (define (loop qualifiers working-qualifiers)
               (if (null? qualifiers) working-qualifiers
                 (let* ([good-qualifier? (map good? (map (lambda (q)
                                                           (cons q working-qualifiers))
                                                         qualifiers))]
                        [next-qualifiers
                          (map cadr (filter (lambda (x)
                                              (not (car x)))
                                            (zip good-qualifier? qualifiers)))]
                        [next-working 
                          (append 
                            (map cadr (filter car (zip good-qualifier? qualifiers)))
                            working-qualifiers)])
                   (if (equal? next-qualifiers qualifiers) working-qualifiers
                     (loop next-qualifiers next-working)))))
             (loop qualifiers '()))

           (define subtype-constr-table (map subtype-constr? initial-sol))

           (define (subtype-constr? c) (subtype? (cadr c)))
           (define (convert-raw c) c)

           (define (satisfied? z3-res is-subtype-constr?)
             (or (not is-subtype-constr?)
                 (and (valid? z3-res)
                      is-subtype-constr?)))

           (let* ([progs (map make-smt-prog (lift-invariants2 initial-asn initial-sol var-type-map constraint-types))]
                  [smt-results (map run-z3 progs)])
             (letrec ([loop (lambda (curr-results curr-asn)
                              (pretty-print `(solve-loop sat ,(length (filter (lambda (x) x) (map satisfied? curr-results subtype-constr-table)))
                                                         total ,(length curr-results)
                                                         ,(hash-table->alist curr-asn) ))
                              (let* ([done? (all (lambda (rb) (satisfied? (car rb) (cadr rb)))
                                                 (zip curr-results subtype-constr-table))])
                                (if done? (hash-table->alist curr-asn)
                                  (let* ([next-asn (hash-table-copy curr-asn equal?)]
                                         [next-unsat-idx (first-index-of 
                                                           (lambda (e-b) 
                                                             (not (satisfied? (car e-b) (cadr e-b))))
                                                           (zip curr-results subtype-constr-table))]
                                         [raw-constr (convert-raw (list-ref initial-sol next-unsat-idx))]
                                         [vars (list-ref responsible-variables next-unsat-idx)])
                                    (if (null? vars) 'no-soln-var-not-found
                                      (let* ([var (car vars)]
                                             [raw-constr-type (list-ref constraint-types next-unsat-idx)]
                                             [weakened-qualifiers (weaken next-asn var (hash-table-ref curr-asn var) raw-constr raw-constr-type)]
                                             [void (hash-table-set! next-asn var weakened-qualifiers)]
                                             [contradict? (not (valid? (re-project-single raw-constr raw-constr-type next-asn)))])
                                        (if contradict? 'no-soln-contradict
                                          (loop 
                                            (re-project next-asn)
                                            next-asn))))))))])
               (loop smt-results initial-asn))))
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

         (define (modify-substitution constraints new-assignment)
           (define (lookup-var v)
             (if (assoc `(,v . Int) new-assignment)
               (assoc `(,v . Int) new-assignment)
               (if (assoc `(,v . Bool) new-assignment)
                 (assoc `(,v . Bool) new-assignment)
                 '())))
           (map (lambda (constraint)
                  (let* ([env (car constraint)]
                         [formula (cadr constraint)]
                         [assignments (caddr constraint)])
                    `(,env ,formula
                           ,(map (lambda (asn)
                                   (let* ([v (caar asn)]
                                          [lookup-res (lookup-var v)])
                                     (if (null? lookup-res)
                                       asn
                                       lookup-res)))
                                 assignments))))))

         (define (label->var-type-map orig-expr label-type-map)
           (filter (lambda (x) (not (null? x)))
                   (map (lambda (l-t)
                          (let* ([l (car l-t)]
                                 [type (cdr l-t)]
                                 [my-subexpr (expr-search l orig-expr)])
                            (if (ref? my-subexpr)
                              (cons (ref->var my-subexpr) type)
                              '())))
                        label-type-map)))

         (define (make-initial-substitution expr label-type-map constraints constraint-types)

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
                 (possible-primitive-predicates 
                   (cons 'V (filter (lambda (v) (and (assoc v var-type-map)
                                                     (equal? 'Int (cdr (assoc v var-type-map))))) 
                                    variables)))))
             (define (get-variables constr)
               (define (loop c)
                 (cond [(refinement? c) '()]
                       [(subtype? c) (get-variables (cadr c))]
                       [(template? c) (if (and (template-variable? (cadr c))
                                               (equal? 'Int (caddr c)))
                                        (list (cadr c))
                                        ;; (list (cons (cadr c) (caddr c)))
                                        '())]
                       [(arrow-type? c) (append (get-variables (arrow-type-arg c))
                                                (get-variables (arrow-type-res c)))]
                       [(parametric-type? c) (apply append (map get-variables (cdr c)))]
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

         (define (to-assignment sub) 
           (define res (make-hash-table equal?))
           (for-each (lambda (asn)
                       (hash-table-set! res (car asn) (cdr asn)))
                     (apply append (map caddr sub)))
           res)

         (define (get-responsible-variables cs)
           (define (variables-of constr)
             (cond [(template? constr)
                    (if (and (template-variable? (cadr constr))
                             (equal? 'Int (caddr constr)))
                      (list (cadr constr))
                      '())]
                   [(parametric-type? constr)
                    (apply append (map variables-of (cdr constr)))]
                   [(substitution? constr)
                    (variables-of (caddr constr))]
                   [(refinement? constr) '()]
                   [else '()]))
           (map (lambda (entail)
                  (let* ([c (caddr entail)])
                    (if (subtype? c)
                      (variables-of (caddr c))
                      (variables-of c))))
                cs))

         (define (get-constraint-types cs)
           (define (type-of constr)
             (cond [(template? constr)
                    (caddr constr)]
                   [(substitution? constr)
                    (type-of (caddr constr))]
                   [(refinement? constr)
                    (type-of (cadr (cadr constr)))]
                   [else constr]))
           (map (lambda (entail)
                  (let* ([c (caddr entail)])
                    (if (subtype? c)
                      (type-of (cadr c))
                      (type-of c))))
                cs))

         (define (lift-invariants2 asn constraints var-type-map constraint-types)
           (define (lookup-var v)
             (let* ([lookup-res (hash-table-ref asn v (lambda () '()))])
               lookup-res))
           (define (subtype? constr)
             (and (pair? constr)
                  (equal? '<: (car constr))))

           (define (L t)
             (cond [(subtype? t)
                    `(<: ,(L (cadr t))
                         ,(L (caddr t)))]
                   [(arrow-type? t)
                    `(-> ,(L (arrow-type-arg t))
                         ,(L (arrow-type-res t)))]
                   [(parametric-type? t)
                    `(,(car t) ,@(map L (cdr t)))]
                   [(template? t)
                    (let ([t* (cadr t)]
                          [assoc-var (cadddr t)])
                      `(: ,(cond  [(refinement? t*) t*]
                                  [(and (template-variable? t*) 
                                        (equal? 'Int (caddr t)))
                                   (let* ([lookup-result (lookup-var t*)])
                                     `(rf (V unused)
                                          (and ,@lookup-result)))]
                                  [else t*])
                          ,(caddr t)
                          ,(cadddr t)))]
                   [(substitution? t)
                    (let* ([body (L (caddr t))]
                           [bindings (map (lambda (var-val)
                                            (let* ([val (let* ([res (de-label (cadr var-val) '())])
                                                          (if (and (const? (cadr var-val))
                                                                   (null? (const->val (cadr var-val))))
                                                            'nil
                                                            res))])
                                              (cons (car var-val) val)))
                                          (cadr t))]
                           [res (search-and-replace bindings body)])
                      ;; (pretty-print `(bindings ,(cadr t) body ,body ))
                      ;; (pretty-print `(after-sub ,res))
                      res)]
                   [else t]))

           (define (guard-predicate? binding)
             (equal? "E" (substring (symbol->string (car binding)) 0 1)))

           (define (replace-refinement bindings body)
             (cond [(template? body)
                    (let* ([refinement (cadr body)])
                      (replace-refinement bindings refinement))]
                   [(refinement? body)
                    (let* ([to-replace (caddr body)])
                      (search-and-replace bindings to-replace))]
                   [(parametric-type? body)
                    (let* ([to-replace (cdr body)])
                      `(and ,@(map (lambda (x) (replace-refinement bindings x)) to-replace)))]
                   [(or (type-variable? body)
                        (template-variable? body)) 'true]
                   [else body]))
           (define (refinement-binding? binding)
             (refinement? (cdr binding)))
           (define (transform-refinement v ref)
             (replace-refinement `((V . ,v)) ref))
           (define (template-binding? binding) 
             ;; (pretty-print `(template-binding? ,binding))
             (or (parametric-type? (cdr binding))
                 (template? (cdr binding))))
           (define (transform-template v temp)
             (replace-refinement `((V . ,v)) temp))
           (define (transform-guard-predicate pred)
             (de-label pred '()))
           (define (remove-irrelevant-bindings env)
             (define (unit? b) (null? (car b)))
             (define (arrow-binding? b) (arrow-type? (cdr b)))
             (define (poly? b) (polymorphic-refinement? (cdr b)))
             (define (polymorphic-refinement? t)
               (cond [(template? t) (polymorphic? (caddr t))]
                     [(refinement? t) (polymorphic? (cadr (cadr t)))]
                     [else (polymorphic? t)]))
             (filter (lambda (x) 
                       (begin 
                         ;;(pretty-print `(x: ,x))
                         (and
                           ;; (not (poly? x))
                           (not (arrow-binding? x))
                           (not (unit? x)))))
                     env))
           (define (transform-guards env)
             (map (lambda (binding)
                    (cond 
                      [(template-binding? binding) (cons (car binding) (disambiguate-nil (transform-template (car binding) (cdr binding))))]
                      [(refinement-binding? binding) (cons (car binding) (disambiguate-nil (transform-refinement (car binding) (cdr binding))))]
                      [(guard-predicate? binding) (cons (car binding) (disambiguate-nil (transform-guard-predicate (cdr binding))))]
                      [else binding]))
                  env))

           (define (to-EUFA constr)
             (cond [(subtype? constr)
                    `(=> ,(to-EUFA (cadr constr))
                         ,(to-EUFA (caddr constr)))]
                   [(type-variable? constr) 'true]
                   [(parametric-type? constr)
                    `(and ,@(map to-EUFA (cdr constr)))]
                   [(template? constr)
                    (if (template-variable? (cadr constr)) 'true
                      (to-EUFA (cadr constr)))]
                   [(refinement? constr)
                    (let* ([conj (caddr constr)])
                      (if (or (equal? '(and) conj)
                              (equal? '() conj))
                        'true
                        conj))]
                   [else constr]))

               (define (is-var? v) (and (symbol? v) (assoc v var-type-map)))
               (define (get-vars e)
                 (cond [(pair? e) (apply append (map get-vars (cdr e)))]
                       [(symbol? e) (if (is-var? e) (list e) '())]
                       [else '()]))
           (define (remove-polymorphic-clauses env)
             (define (not-polymorphic? binding)
               (let* ([expr (cdr binding)]
                      [expr-vars (get-vars expr)])
                 (not (some polymorphic? (map (lambda (x) (cdr (assoc x var-type-map)))
                                             expr-vars)))))
             (filter not-polymorphic? env))

           (define (has-nil? expr)
             (cond [(pair? expr)
                    (or (has-nil? (car expr))
                        (has-nil? (cdr expr)))]
                   [(symbol? expr) (equal? 'nil expr)]
                   [else #f]))

           (define (disambiguate-nil expr-with-nil)
             (if (has-nil? expr-with-nil)
               (let* ([vars (get-vars expr-with-nil)]
                      [list-typed-var (car (filter (lambda (v) (let ([t (cdr (assoc v var-type-map))])
                                                            (if (pair? t) (equal? (car t) 'Lst)
                                                              #f)))
                                              vars))]
                      [type-of-that (cdr (assoc list-typed-var var-type-map))])
                 (search-and-replace `((nil . (as nil ,type-of-that))) expr-with-nil))
               expr-with-nil))

           (define (get-polymorphic t)
             (cond [(type-variable? t) (list t)]
                   [(primitive-type? t) '()]
                   [(arrow-type? t)
                    (append (get-polymorphic (arrow-type-arg t))
                            (get-polymorphic (arrow-type-res t)))]
                   [(parametric-type? t)
                    (apply append (map get-polymorphic (cdr t)))]
                   [else '()]))


           (map (lambda (constraint constraint-type)
                  (let* ([sorts-to-declare '()]
                         [env (map (lambda (var-val)
                                     `(,(car var-val) . ,(L (cdr var-val))))
                                   (car constraint))]
                         ;; [void (pretty-print `(dirty-env ,env))]
                         [cleaned-env (transform-guards (remove-irrelevant-bindings env))]
                         ;; [cleaned-env* (remove-polymorphic-clauses cleaned-env)]
                         [cleaned-env* ((lambda (x) x) cleaned-env)]
                         ;; [void (pretty-print `(clean-env ,cleaned-env))]
                         [as-EUFA-conj (if (null? cleaned-env*) 'true
                                         (cons 'and (map (lambda (e)
                                                           (if (equal? '(and) e) 'true e))
                                                         (map cdr cleaned-env*))))]
                         [constr (cadr constraint)])
                    `(smt
                       (decls
                         ,@(if (not (polymorphic? constraint-type))
                             (list `(declare-const V ,constraint-type)) 
                             (let* ([sorts (get-polymorphic constraint-type)])
                               (for-each (lambda (sort)
                                           (if (not (assoc sort sorts-to-declare))
                                             (set! sorts-to-declare (cons
                                                                      (cons sort `(declare-sort ,sort 0))
                                                                      sorts-to-declare))))
                                         sorts)
                               (append
                                 (map (lambda (s) (cdr (assoc s sorts-to-declare)))
                                      sorts)
                                 (list `(declare-const V ,constraint-type)))))
                         ,@(apply append (map (lambda (var-val)
                                                (let* ([type (cdr (assoc (car var-val) var-type-map))])
                                                  (if (arrow-type? type) '()
                                                    (if (not (polymorphic? type))
                                                      (list `(declare-const ,(car var-val) ,type))
                                                      (let* ([sorts (get-polymorphic type)])
                                                        '(for-each (lambda (sort)
                                                                     (if (not (assoc sort sorts-to-declare))
                                                                       (set! sorts-to-declare (cons sort `(declare-sort ,sort 0)))))
                                                                   sorts)
                                                        (append
                                                          (apply append (map (lambda (s) 
                                                                               (if (not (assoc s sorts-to-declare))
                                                                                 (begin
                                                                                   (set! sorts-to-declare (cons (cons s `(declare-sort ,s 0))
                                                                                                                sorts-to-declare))
                                                                                   (list `(declare-sort ,s 0)) )
                                                                                 '()))
                                                                             sorts))
                                                          (list `(declare-const ,(car var-val) ,type))))))))
                                              (filter (lambda (binding)
                                                        (and 
                                                          ;; (if (assoc (car binding) var-type-map) (not (polymorphic? (cdr (assoc (car binding) var-type-map)))) #t)
                                                          (not (arrow-type? (cdr binding)))
                                                          (not (equal? 'unit (car binding)))
                                                          (not (guard-predicate? binding))))
                                                      cleaned-env*))))
                       (body
                         (entail 
                           ,as-EUFA-conj
                           ,(to-EUFA (L constr)))))))
                constraints constraint-types))

         (define (make-smt-prog smt-struct)
           (define (entailment? e)
             (and (pair? e) (equal? 'entail (car e))))
           (define (to-smt e)
             (cond [(entailment? e)
                    `(assert (and ,(cadr e)
                                  (not ,(caddr e))))]
                   [else e]))
           (let* ([decls (cdr (cadr smt-struct))]
                  [body (cdr (caddr smt-struct))])
             `((declare-sort Clo 0)
               (declare-datatypes (T) ((Lst nil (cons (car T) (cdr Lst)))))
               ,@decls ,@(map to-smt body) (check-sat) (get-model))))

         (define (weaken sub bad-qualifiers)
           '())

         )
