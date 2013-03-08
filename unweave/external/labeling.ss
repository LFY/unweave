#!r6rs

(library

 (unweave external labeling)

 (export label-transform
         de-label
         de-label-env
         free-variables
         referenced-variables)

 (import (rnrs)
         (scheme-tools srfi-compat :1)
         (unweave external church-syntax))

 ;; Labeling transform===========================================================

 (define label-ctr 0)

 (define (next-label)
   (let* ([answer (+ 1 label-ctr)])
     (begin
       (set! label-ctr answer)
       (string->symbol (string-append "a" (number->string answer))))))

 (define (label-transform sexpr)
   (define first car)
   (define second cadr)
   (define third caddr)
   (define fourth cadddr)
   (define (fifth lst) (list-ref lst 4))
   (define (sixth lst) (list-ref lst 5))
   (define (seventh lst) (list-ref lst 6))
   (define (eighth lst) (list-ref lst 7))
   (define (ninth lst) (list-ref lst 8))
   (define (tenth lst) (list-ref lst 9))

   (define rest cdr)
   (define pair cons)

   (define false #f)
   (define true #t)

   (define (tagged-list? exp tag)
     (if (pair? exp)
         (equal? (car exp) tag)
         false))

   (define (mem? sexpr) (tagged-list? sexpr 'mem))
   (define (lambda? exp) (tagged-list? exp 'lambda))
   (define (assert? exp) (tagged-list? exp 'assert))
   (define (lambda-parameters exp) (cadr exp))
   (define (lambda-body exp) (caddr exp))
   (define (begin? exp) (tagged-list? exp 'begin))
   (define (if? exp) (tagged-list? exp 'if))
   (define (application? exp) (pair? exp))
   (define (letrec? exp) (tagged-list? exp 'letrec))

   (define (cond? e) (if (pair? e) (equal? (car e) 'cond) #f))
   (define (cond->ifs expr)
     (letrec
         ([conds (cdr expr)])
       (if (equal? 'else (caar conds))
           (cadr (car conds))
           `(if ,@(car conds)
                ,(cond->ifs conds)))))

   (define (label sexpr)
     (cond
      [(assert? sexpr) `(assert ,(next-label) ,@(map label (rest sexpr)))]
      [(begin? sexpr) `(begin ,(next-label) ,@(map label (rest sexpr)))]
      [(quoted? sexpr) `(const ,(next-label) ,(cadr sexpr))]
      [(cond? sexpr) (label (cond->ifs sexpr))]
      [(if? sexpr) `(if ,(next-label) ,@(map label (rest sexpr)))]
      [(letrec? sexpr) `(letrec ,(next-label)
                          ,(map (lambda (binding) (list (first binding) (label (second binding)))) (second sexpr))
                          ,(label (third sexpr)))]
      [(lambda? sexpr) `(lambda ,(next-label) ,(lambda-parameters sexpr)
                                ,(label (lambda-body sexpr))
                                ,@(if (> (length sexpr) 3)
                                      (list (list-ref sexpr 3))
                                      '()))]
      [(xrp? sexpr) `(xrp ,(next-label) ,@(map label (cdr sexpr)))]
      [(xrps? sexpr) `(xrps ,(next-label) ,@(map label (cdr sexpr)))]
      [(xrp+init? sexpr) `(xrp+init ,(next-label) ,@(map label (cdr sexpr)))]
      [(factor? sexpr) `(factor ,(next-label) ,(lambda-parameters sexpr) ,(label (lambda-body sexpr)))]
      [(application? sexpr)
       `(call ,(next-label)
              ,(label (first sexpr))
              ,@(map label (rest sexpr)))]
      [(symbol? sexpr) `(ref ,(next-label) ,sexpr)]
      [(or
        (number? sexpr)
        (string? sexpr)
        (null? sexpr)) `(const ,(next-label) ,sexpr)]
      [else `(const ,(next-label) ,sexpr)] ))
   (label sexpr))
(define (referenced-variables expr bound primitive-env)
    (define test-env (map list bound))
    (define free '())
    (define (E ex env)
      (cond [(if? ex) (explode-if ex (lambda (l c t e) `(if ,(E c env) ,(E t env) ,(E e env))))]
            [(or (factor-closure? ex) (closure? ex)) (explode-closure (lambda (l e2)
                                              (E l (append e2 env))))]
            [(lambda? ex) (explode-lambda ex (lambda (l vs c) `(lambda ,vs ,(E c (append (map (lambda (v) (list v)) vs) env)))))]
            [(letrec? ex) (explode-letrec ex (lambda (l bs call) (let* ([local-binding-env (fold (lambda (b e) (extend e (car b) (E (cadr b) e))) env bs)])
                                                                   (E call local-binding-env))))]
            [(call? ex) (explode-call ex (lambda (l f vs) (begin (E f env) (map (lambda (e) (E e env)) vs))))]
            [(ref? ex) (set! free (cons (ref->var ex) free))]
            [(xrp? ex) (explode-xrp ex (lambda (l s n p ps)
                                         (for-each (lambda (x)
                                                     (E x env))
                                                   ps)))]
            [(xrps? ex) (explode-xrps ex (lambda (l s n p ps)
                                           (for-each (lambda (x)
                                                       (E x env))
                                                     ps)))]
            [(xrp+init? ex) (explode-xrp+init ex (lambda (l s n p initval ps)
                                                   (for-each (lambda (x)
                                                               (E x env))
                                                             (cons initval ps))))]
            [(const? ex) '()]
            [else '()]) )
    (begin
      (E expr test-env)
      free))
 ;; Delabeling transform=========================================================
 (define (free-variables expr bound primitive-env)
   (define test-env (map list bound))
   (define free '())
   (define (E ex env)
     (cond [(if? ex) (explode-if ex (lambda (l c t e) `(if ,(E c env) ,(E t env) ,(E e env))))]
           [(or (factor-closure? ex) (closure? ex)) (explode-closure (lambda (l e2)
                                                                       (E l (append e2 env))))]
           [(lambda? ex) (explode-lambda ex (lambda (l vs c) `(lambda ,vs ,(E c (append (map (lambda (v) (list v)) vs) env)))))]
           [(letrec? ex) (explode-letrec ex (lambda (l bs call) (let* ([local-binding-env (fold (lambda (b e) (extend e (car b) (E (cadr b) e))) env bs)])
                                                                  (E call local-binding-env))))]
           [(call? ex) (explode-call ex (lambda (l f vs) (begin (E f env) (map (lambda (e) (E e env)) vs))))]
           [(ref? ex) (let* ([lookup-res (lookup env (ref->var ex))]
                             [lookup-res2 (lookup primitive-env (ref->var ex))])
                        (if (and (not-found? lookup-res)
                                 (not-found? lookup-res2))
                            (set! free (cons (ref->var ex) free)) '()))]
           [(xrp? ex) '()]
           [(xrps? ex) '()]
           [(xrp+init? ex) '()]
           [(const? ex) '()]
           [else '()]) )
   (begin
     (E expr test-env)
     free))
 (define (de-label ex start-env)
   (define (get-free vars expr)
     (define test-env (map list vars))
     (define free '())
     (define (E ex env)
       (cond [(if? ex) (explode-if ex (lambda (l c t e) `(if ,(E c env) ,(E t env) ,(E e env))))]
             [(or (factor-closure? ex) (closure? ex)) (explode-closure (lambda (l e2)
                                                                         (E l (append e2 env))))]
             [(lambda? ex) (explode-lambda ex (lambda (l vs c) `(lambda ,vs ,(E c (append (map (lambda (v) (list v)) vs) env)))))]
             [(letrec? ex) (explode-letrec ex (lambda (l bs call) (let* ([local-binding-env (fold (lambda (b e) (extend e (car b) (E (cadr b) e))) env bs)])
                                                                    (E call local-binding-env))))]
             [(call? ex) (explode-call ex (lambda (l f vs) (begin (E f env) (map (lambda (e) (E e env)) vs))))]
             [(ref? ex) (let* ([lookup-res (lookup env (ref->var ex))]
                               [lookup-res2 (lookup start-env (ref->var ex))])
                          (if (and (not-found? lookup-res)
                                   (not-found? lookup-res2))
                              (set! free (cons (ref->var ex) free)) '()))]
             [(xrp? ex) '()]
             [(xrps? ex) '()]
             [(xrp+init? ex) '()]
             [(const? ex) '()]
             [else '()]) )
     (begin
       (E expr test-env)
       free))

   (define (var? x)
     (and (symbol? x)
          (member (substring (symbol->string x) 0 1)
                  (list "L" "R" "X" "A" "V" "P" "R" "Q" "S"))))

   (define (D ex)
     (cond [(if? ex) (explode-if ex (lambda (l c t e) `(if ,(D c) ,(D t) ,(D e))))]
           [(lambda? ex) (explode-lambda ex (lambda (l vs c) `(lambda ,vs ,(D c))))]
           [(or (factor-closure? ex) (closure? ex)) (explode-closure ex (lambda (lam env2)
                                                                          (let* ([vars-lam (explode-lambda lam (lambda (l vs c)
                                                                                                                 (list vs c)))]
                                                                                 [free (free-variables (car vars-lam) (cadr vars-lam) start-env)]
                                                                                 [extra-bindings (map (lambda (fv) (list fv (lookup env2 fv))) free)]
                                                                                 [l-term `(lambda ,(car vars-lam)
                                                                                            (let ,extra-bindings
                                                                                              ,(D (cadr vars-lam))))])
                                                                            (if (factor-closure? ex)
                                                                                `(factor ,l-term) l-term)
                                                                            )))]
           [(letrec? ex) (explode-letrec ex (lambda (l bs call) `(letrec
                                                                ,(map (lambda (b) (list (car b) (D (cadr b)))) bs)
                                                              ,(D call))))]
           [(call? ex) (explode-call ex (lambda (l f vs) `(,(D f) ,@(map D vs))))]
           [(ref? ex) (ref->var ex)]
           [(xrp? ex) (explode-xrp ex (lambda (l sc smp prop params)
                                       `(xrp ,@params)))]
           [(xrps? ex) `(quote THIS-SHOULD-NOT-SHOW-UP)]
           [(xrp+init? ex) `(quote THIS-SHOULD-NOT-SHOW-UP)]
           [(factor? ex) (explode-factor ex (lambda (lab formals f) `(factor (lambda ,formals ,(D f)))))]
           [(const? ex) (let* ([v (const->val ex)])
                          (if (null? v) '(quote ()) (D v)))]
           [(rv? ex) (explode-xrp-trace ex (lambda (addr var sampler-name params val score-fx-name prop-fx-name)
                                             ;; `(begin
                                             ;;   ;;(set! score (+ score (,score-fx-name (list ,@(map D params)) ,var)))
                                             ;;   ,var)))]
                                             `(xrp+score ,score-fx-name ,var ,@(map D params))))]
           ;;var))]
           ;; (explode-xrp-trace ex (lambda (addr var prop-fx-name params val score-fx-name)
           ;;    `(let* ([val (xrp+score ,var ,prop-fx-name ,score-fx-name ,@(map D params))])
           ;;       (set! ,var val)
           ;;       val)))]
           [(or
             (var? ex)
             (number? ex)
             (boolean? ex)
             (string? ex)) ex]
           [else
            `(quote ,ex)]))
   (D ex))

 (define (de-label-env e start-env)
   (map (lambda (v-e) (cons (car v-e) (de-label (cdr v-e) start-env))) e))


 )
