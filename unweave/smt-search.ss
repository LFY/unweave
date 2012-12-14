#!r6rs
(library (unweave smt-search)
         (export smt-solve
                 run-smt
                 smt-mh-query)

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

                 (unweave z3)

                 (unweave util))

         ;; Our state
         (define (smt-evaluator ex env addr)

           (define (type-parameter? s)
             (member s '(A B C D E F G H I J K L M)))

           (define (contains-type-parameter? t)
             (if (null? t) #f
               (if (pair? t)
                 (or (contains-type-parameter? (car t))
                     (contains-type-parameter? (cdr t)))
                 (type-parameter? t))))

           ;; Assertions (for SMT solver)

           (define stmts '())
           (define scoring-stmts '())
           (define continue-thunks '())
           (define deletion-thunks '())

           (define symbol-maker-map (make-hash-table equal?))

           (define addr-var-map (make-hash-table equal?))

           (define var-val-map (make-hash-table equal?))
           (define var-type-map (make-hash-table equal?))
           (define lazy-map (make-hash-table equal?))

           ;; Assigns a function call name (with variable arguments, etc) to each call variable.
           (define call-name-map (make-hash-table equal?))

           (define (addr->var addr prefix)
             (hash-table-ref addr-var-map 
                             (list addr prefix)
                             (lambda () 
                               (let* ([var-maker (hash-table-ref symbol-maker-map prefix 
                                                                 (lambda ()
                                                                   (let* ([var-maker (symbol-maker prefix)])
                                                                     (hash-table-set! symbol-maker-map prefix var-maker)
                                                                     var-maker)))]
                                      [var (var-maker)])
                                 (hash-table-set! addr-var-map (list addr prefix) var) 
                                 var))))

           (define (var? v) (and (symbol? v) (or (equal? "C" (substring (symbol->string v) 0 1))
                                                 (equal? "V" (substring (symbol->string v) 0 1))
                                                 (equal? "E" (substring (symbol->string v) 0 1))
                                                 (equal? "A" (substring (symbol->string v) 0 1))
                                                 (equal? "X" (substring (symbol->string v) 0 1))
                                                 (equal? "Y" (substring (symbol->string v) 0 1))
                                                 (equal? "S" (substring (symbol->string v) 0 1)))))

           (define (inst-type! var val)
             (if (and (hash-table-exists? var-type-map var)
                      (not (contains-type-parameter? (hash-table-ref var-type-map var)))
                      (contains-type-parameter? val))
               '()
               (hash-table-set! var-type-map var val)))

           (define (inst-val! var val)
             (hash-table-set! var-val-map var val))

           (define (val->type val)

             (define (proper-list? xs)
               (if (or (null? xs) (pair? xs))
                 (if (null? (cdr xs)) 
                   #t
                   (proper-list? (cdr xs)))
                 #f))

             (define (list->ground-type xs)
               (let* ([elt-type (val->type (car xs))])
                 `(Lst ,elt-type)))

             ;; FIXME
             (define (improper-list->ground-type xs)
               `(ImpLst ,(cadr (list->ground-type xs))))

             (let* ([result (cond [(pair? val) (if (proper-list? val) 
                                                 (list->ground-type val)
                                                 (improper-list->ground-type val))]
                                  [(null? val) '(Lst A)]
                                  [(number? val) (cond [(exact? val) 'Int]
                                                       [(inexact? val) 'Real]
                                                       [else 'Real])]
                                  [(boolean? val) 'Bool]
                                  [(string? val) 'String]
                                  [(symbol? val) 'Symbol]
                                  [else (begin
                                          ;; (pretty-print `(unknown! ,val))
                                          'UNKNOWN-TYPE)])])

               ;; (pretty-print `(val->type ,val ,result))
               result))

           (define (inst-val-type! var val)
             (let* ([type (val->type val)])
               (inst-val! var val)
               (inst-type! var type)
               var))

           (define (inst-lazy-val! var val)
             (hash-table-set! lazy-map var val))

           (define (lazy-var? var)
             (hash-table-exists? lazy-map var))

           (define (get-val var)
             (if (var? var)
               (hash-table-ref var-val-map var (lambda () `(not-found: ,var)))
               var))

           (define (get-type var)
             (if (var? var)
               (hash-table-ref var-type-map var (lambda () 'unknown))
               (val->type var)))

           (define (new-call-name addr) (addr->var addr 'F))
           (define (next-control addr) (addr->var addr 'C))
           (define (next-ret addr) (addr->var addr 'Y))
           (define (next-choice addr) (addr->var addr 'X))
           (define (next-assert addr) (addr->var addr 'A))

           ;; choice existence variables: take the current assignment to control
           ;; variables (which cover all possible control paths in the current
           ;; unfolding). then, when we encounter xrp during evaluation, inspect the
           ;; current set of C# variables, and instantiate an existence variable that is
           ;; true iff the current assignment to control variables matches.  then we
           ;; have a set of variables plus an SMT formula that expresses all possible
           ;; executions up to a particular depth.

           ;; note that this is a compact way to represent a very large set of traces.
           ;; one can flip through lots of structures simply by assigning different values to the control variables.

           (define (next-choice-existence addr) (addr->var addr 'E))
           (define (next-call addr) (addr->var addr 'V))

           (define (next-score addr) (addr->var addr 'S))

           (define (next-recursion-flag addr) (addr->var addr 'R))

           (define (add-stmt-once! stmt) (if (not (member stmt stmts)) (add-stmt! stmt) '()))
           (define (add-stmt! stmt) (set! stmts (cons stmt stmts)))
           (define (add-scoring-stmt! stmt) (set! scoring-stmts (cons stmt scoring-stmts)))

           (define (lookup cxt label) (let* ([lk (assoc label cxt)]) (if lk (cdr lk) 'not-found)))

           (define (rv? v) (and (var? v) (equal? "X" (substring (symbol->string v) 0 1))))
           (define (control-var? v) (and (var? v) (equal? "C" (substring (symbol->string v) 0 1))))

           (define (get-assignment)
             (filter (lambda (var-val)
                       (let* ([var (car var-val)]
                              [val (cdr var-val)])
                         (rv? var)))
                     (hash-table->alist var-val-map)))

           (define (addr->func-name addr)
             (string->symbol (apply string-append (map symbol->string addr))))

           (define (env-update var val env)
             (if (assoc var env)
               (map (lambda (var-val)
                      (if (equal? var (car var-val)) 
                        `(,var . ,val)
                        var-val))
                    env)
               (cons `(,var . ,val) env)))

           (define (infer-return-type prim var-vals) 
             ;; (pretty-print `(infer ,prim ,@var-vals))
             (let* ([types (map (lambda (var-val)
                                  (if (var? var-val)
                                    (get-type var-val)
                                    (val->type var-val)))
                                var-vals)])
               (cond [(member prim '(+ - / *)) (if (all (lambda (x) (equal? x 'Int)) types) 'Int 'Real)]
                     [(member prim '(and or not)) 'Bool]
                     [(equal? prim 'cons) (let* ([type
                                                   `(Lst ,(let* ([var-val (car var-vals)])
                                                            (if (var? var-val) 
                                                              (get-type var-val)
                                                              (val->type var-val))))]
                                                 [rest-var-val (cadr var-vals)])
                                            (if (var? rest-var-val)
                                              (begin
                                                ;; (pretty-print `(inst-type! ,var-vals ,rest-var-val ,type))
                                                (inst-type! rest-var-val type)))
                                            type)]
                     [(equal? prim 'cdr) (let* ([var-val (car var-vals)])
                                           (if (var? var-val)
                                             (get-type var-val)
                                             (val->type var-val)))]
                     [(equal? prim 'car) (let* ([var-val (car var-vals)])
                                           (let* ([type (if (var? var-val)
                                                          (get-type var-val)
                                                          (val->type var-val))])
                                             (cadr type)))]
                     [(equal? prim 'null?) 'Bool]
                     [(member prim '(> < = <= >=)) 'Bool]
                     [else (begin
                             ;; (pretty-print `(unknown: (,prim ,@var-vals)))
                             'UNKNOWN-TYPE)])))

           (define (convert-prim f args)
             (if (equal? 'null? f) 
               (let* ([arg (car args)]
                      [type (hash-table-ref var-type-map arg)])
                 `(= (as nil ,type) ,arg))
               `(,f ,@args)))

           (define (E ex env addr lazy? control-env) 
             (cond
               ;; Associate a SMT variable with every address.
               ;; FIXME: Account for evaluating if-statements in lazy mode
               ;; if we're lazy, we'd like to still record if-statements, but not actually use the real value of the control variable.
               [(if? ex) (explode-if ex (lambda (l c t e) 
                                          (if (not lazy?)
                                            (let* ([Cv (next-control addr)]
                                                   ;; invariant: once we've retrieved the variable from calling E on something, we also have access to the actual sampled value.
                                                   [Vv (E c env addr lazy? control-env)]
                                                   ;; record the value of the control variable.
                                                   [void (inst-val-type! Cv (get-val Vv))]
                                                   [eval-T? (get-val Vv)]
                                                   [Rv (next-ret addr)]
                                                   [Tv (E t env (cons l addr) (not eval-T?) (env-update Cv #t control-env))]
                                                   [Ev (E e env (cons l addr) eval-T? (env-update Cv #f control-env))])
                                              (add-stmt! `(assert (and (= ,Cv ,Vv) (=> ,Cv (= ,Rv ,Tv)) ;; constraint representing then-branch
                                                                       (=> (not ,Cv) (= ,Rv ,Ev))))) ;; else-branch
                                              (inst-type! Rv (if (contains-type-parameter? (get-type Tv))
                                                               (get-type Ev)
                                                               (get-type Tv)))
                                              ;; (pretty-print `(inst-type! ,Rv (if ,eval-T? ,(get-type Tv) ,(get-type Ev))))
                                              (inst-val! Rv (if eval-T? (get-val Tv) (get-val Ev)))
                                              Rv)
                                            (let* ([Cv (next-control addr)]
                                                   ;; invariant: once we've retrieved the variable from calling E on something, we also have access to the actual sampled value.
                                                   [Vv (E c env addr lazy? control-env)]
                                                   ;; record the value of the control variable.
                                                   [void (inst-type! Cv 'Bool)]
                                                   [Rv (next-ret addr)]
                                                   [Tv (E t env (cons l addr) #t (env-update Cv #t control-env))]
                                                   [Ev (E e env (cons l addr) #t (env-update Cv #f control-env))])
                                              (add-stmt! `(assert (and (= ,Cv ,Vv) (=> ,Cv (= ,Rv ,Tv)) ;; constraint representing then-branch
                                                                       (=> (not ,Cv) (= ,Rv ,Ev))))) ;; else-branch
                                              (inst-type! Rv (if (contains-type-parameter? (get-type Tv))
                                                               (get-type Ev)
                                                               (get-type Tv)))
                                              Rv)
                                            )))]
               [(assert? ex) (explode-assert ex (lambda (l p q)
                                                  (let* ([Av (next-assert addr)]
                                                         [Pv (E p env (cons l addr) lazy? control-env)]
                                                         [Qv (E `(call ,l ,q ,Pv) env (cons 'q (cons l addr)) lazy? control-env)])
                                                    (inst-type! Av 'Bool)
                                                    (add-stmt!  `(assert (and (= ,Av ,Qv) (= ,Av #t))))
                                                    Pv)))]
               [(lambda? ex) (explode-lambda ex (lambda (l vs c) `(closure (lambda ,l ,vs ,c ,@(if (has-type-annotation? ex) (list (lambda->return-type ex)) '())) ,env)))]
               [(factor? ex) (explode-factor ex (lambda (lab formals call) 
                                                  `(factor-closure (lambda ,lab ,(cons 'temp formals)
                                                                     (call ,lab (ref ,lab *) (ref ,lab temp) ,call)) ,env)))]
               [(letrec? ex) (explode-letrec ex (lambda (l bs call)
                                                  (let* ([local-binding-env
                                                           (fold (lambda (b e)
                                                                   (extend e (car b) (E (cadr b) e addr lazy? control-env)))
                                                                 env bs)]
                                                         [res (E call local-binding-env addr lazy? control-env)])
                                                    res)))]
               [(rv? ex) (rv->val ex)]
               [(call? ex) (explode-call ex (lambda (l f vs) 
                                              (let* ([Vv (next-call (cons l addr))]
                                                     [proc (E f env (cons l addr) lazy? control-env)]
                                                     [vals (map (lambda (v) (E v env (cons l addr) lazy? control-env)) vs)])
                                                ;; (pretty-print `(call ,Vv ,f ,vals))
                                                (cond [(or (factor-closure? proc)
                                                           (closure? proc)) 
                                                       (explode-closure proc (lambda (lam env2)
                                                                               (let* ([combined-env (append (if (list? (lambda->formals lam))
                                                                                                              (map cons (lambda->formals lam) 
                                                                                                                   (if (factor-closure? proc)
                                                                                                                     (append (cons 1.0 (cdr vals))) 
                                                                                                                     vals))
                                                                                                              (cons (lambda->formals lam) vals))
                                                                                                            env2 env)])
                                                                                 (if lazy?
                                                                                   ;; save a thunk that performs the next step of computation.
                                                                                   (let* ([res-thunk (lambda () 
                                                                                                       (let* ([next-res (E (lambda->call lam) combined-env (cons l addr) #t control-env)])
                                                                                                         (add-stmt! `(assert (= ,Vv ,next-res)))
                                                                                                         next-res))]
                                                                                          [void (set! continue-thunks (cons res-thunk continue-thunks))]
                                                                                          [Rv (next-recursion-flag (cons l addr))]
                                                                                          [Fv (new-call-name (cons l addr))])
                                                                                     (let*
                                                                                       ([recursion-condition 
                                                                                          `(assert (= ,Rv ,(if (null? control-env) #t
                                                                                                             `(and ,@(map (lambda (var-val)
                                                                                                                            `(= ,(car var-val) ,(cdr var-val)))
                                                                                                                          control-env)))))]
                                                                                        [recursion-definition `(assert (=> ,Rv (= ,Vv ,(if (null? vals)
                                                                                                                                         Fv
                                                                                                                                         `(,Fv ,@vals)))))])
                                                                                       (inst-type! Rv 'Bool)
                                                                                       (add-stmt! recursion-condition)
                                                                                       (add-stmt! recursion-definition)


                                                                                       (set! continue-thunks (cons res-thunk continue-thunks))

                                                                                       (if (factor-closure? proc)
                                                                                         (let* ([Sv (next-score (cons l addr))]
                                                                                                [scoring-def `(assert (=> ,Rv (= ,Sv ,Vv)))])
                                                                                           (inst-type! Sv 'Real)
                                                                                           (add-scoring-stmt! scoring-def)
                                                                                           (set! deletion-thunks
                                                                                             (cons
                                                                                               (lambda ()
                                                                                                 (set-car! (cdr recursion-condition) #t)
                                                                                                 (set-car! (cdr recursion-definition) #t)
                                                                                                 (set-car! (cdr scoring-def) #t))
                                                                                               deletion-thunks)))
                                                                                         (set! deletion-thunks
                                                                                           (cons
                                                                                             (lambda ()
                                                                                               (set-car! (cdr recursion-condition) #t)
                                                                                               (set-car! (cdr recursion-definition) #t))
                                                                                             deletion-thunks)))
                                                                                       '())

                                                                                     (if (has-type-annotation? lam)
                                                                                       (let* ([type (lambda->return-type lam)])
                                                                                         (inst-type! Vv (last type))
                                                                                         (inst-type! Fv type)))
                                                                                     (inst-lazy-val! Vv `(,(addr->func-name (list (lambda->lab lam))) ,@vals))
                                                                                     Vv)
                                                                                   (let* ([res (E (lambda->call lam) combined-env (cons l addr) lazy? control-env)])
                                                                                     (add-stmt! `(assert (= ,Vv ,res)))
                                                                                     (if (all (lambda (x) (not (lazy-var? x))) vals)
                                                                                       (inst-val-type! Vv (if (var? res) (get-val res) res)))
                                                                                     Vv)))))]
                                                      [(procedure? proc) 
                                                       (begin
                                                         (add-stmt! `(assert (= ,Vv ,(convert-prim (ref->var f) vals))))
                                                         (if lazy?
                                                           (begin
                                                             ;; (pretty-print `(proc-lazy ,Vv ,(ref->var f) ,@vals))
                                                             ;; type inference is needed here (for primitive functions)
                                                             (inst-type! Vv (infer-return-type (ref->var f) vals))
                                                             Vv)
                                                           (begin
                                                             ;; (pretty-print `(proc-eager ,Vv ,(ref->var f) ,@vals))
                                                             (inst-type! Vv (infer-return-type (ref->var f) vals))
                                                             (if (all (lambda (x) (not (lazy-var? x)))
                                                                      vals)
                                                               (inst-val-type! Vv (apply proc (map (lambda (v) (if (var? v) (get-val v) v))
                                                                                                   vals))))
                                                             Vv)))]
                                                      [else 
                                                        (pretty-print `(error-in-call-norm-eval ,proc))
                                                        ]))))]
               [(ref? ex) (let* ([lookup-res (lookup env (ref->var ex))])
                            (if (not-found? lookup-res) 
                              (begin
                                ;; (pretty-print `(not-found: ,lookup-res ,(ref->var ex)))
                                (cond [(rv? lookup-res)
                                       (list-ref lookup-res 5)]
                                      [else lookup-res]))
                              lookup-res))]
               [(xrp? ex) (explode-xrp ex (lambda (lab scorer name prop-fx-name params)
                                            (let* ([Xv (next-choice (cons lab addr))]
                                                   [Ev (next-choice-existence (cons lab addr))]
                                                   [Sv (next-score (cons lab addr))]
                                                   [param-vals (map (lambda (p) (E p env addr lazy? control-env)) params)]) 
                                              (inst-type! Ev 'Bool)
                                              (add-stmt! `(assert (= ,Ev ,(if (null? control-env) #t
                                                                            `(and ,@(map (lambda (var-val)
                                                                                           `(= ,(car var-val) ,(cdr var-val)))
                                                                                         control-env))))))
                                              (add-stmt! `(assert (=> ,Ev (or ,@(map (lambda (v) `(= ,Xv ,v)) param-vals)))))
                                              (inst-type! Sv 'Real)
                                              (add-scoring-stmt! `(assert (=> ,Ev (= ,Sv ,(log (/ 1.0 (length param-vals)))))))
                                              ;; just do a uniform selection for now
                                              (inst-val-type! Xv (uniform-select param-vals))
                                              Xv)))]
               [(const? ex) (explode-const ex (lambda (lab c) (if (null? c) '() c)))]
               [else ex]))
           (let* ([final-var (E ex env addr #f '())])
             (pretty-print `(scoring ,scoring-stmts))
             (letrec ([refresh-state (lambda () 
                                       (make-state (list final-var (hash-table-ref var-val-map final-var))
                                                   var-val-map 
                                                   var-type-map 
                                                   lazy-map 
                                                   continue-thunks 
                                                   deletion-thunks 
                                                   stmts 
                                                   refresh-state))])
               (refresh-state))))

         (define (make-state 
                   final 
                   var-val-map 
                   var-type-map 
                   lazy-map 
                   continue-thunks 
                   deletion-thunks 
                   stmts
                   refresh-state)
           `(,final ,var-val-map ,var-type-map ,lazy-map ,continue-thunks ,deletion-thunks ,stmts ,refresh-state))

         (define (make-list-ref n)
           (lambda (xs) (list-ref xs n)))

         (define state->final (make-list-ref 0))
         (define (state->final-val state)
           (hash-table-ref (state->var-val-map state) (car (state->final state))))
         (define state->var-val-map (make-list-ref 1))
         (define state->var-type-map (make-list-ref 2))
         (define state->lazy-map (make-list-ref 3))
         (define state->continue-thunks (make-list-ref 4))
         (define set-state-continue-thunks! (lambda (state cts) (set-list-elt! state cts 4)))
         (define state->deletion-thunks (make-list-ref 5))
         (define set-state-deletion-thunks! (lambda (state cts) (set-list-elt! state cts 5)))
         (define state->stmts (make-list-ref 6))
         (define state->refresh (make-list-ref 7))

         (define (var-val-map->assignment-constraints var-vals)
           (map (lambda (var-val)
                  (let* ([var (car var-val)]
                         [val (cdr var-val)])
                    `(assert (= ,var ,val))))
                var-vals))

         (define (var-type-map->declarations var-types)
           (map (lambda (var-type)
                  (let* ([var (car var-type)]
                         [type (cdr var-type)])
                    (if (pair? type)
                      (if (equal? '-> (car type))
                        (let* ([type-body (cdr type)])
                          `(declare-fun ,var ,(let* ([arg-type (init type-body)]
                                                     [unit? (and (null? (car arg-type))
                                                                 (= (length arg-type) 1))])
                                                (if unit? '()
                                                  arg-type))
                                        ,(last type-body)))
                        `(declare-const ,var ,type))
                      `(declare-const ,var ,type))))
                var-types))

         (define (state->nonrec-model-finder state extra-stmts)
           (define (convert-null expr)
             (cond [(null? expr) '()]
                   [(pair? expr) (cond [(and (equal? '= (car expr))
                                             (or (null? (cadr expr))
                                                 (null? (caddr expr))))
                                        (let* ([var (if (null? (cadr expr))
                                                      (caddr expr)
                                                      (cadr expr))]
                                               [type (hash-table-ref (state->var-type-map state) var)])
                                          `(= ,(if (null? (cadr expr))
                                                 `(as nil ,type)
                                                 (cadr expr))
                                              ,(if (null? (caddr expr))
                                                 `(as nil ,type)
                                                 (caddr expr))))]
                                       [(and (equal? '= (car expr))
                                             (pair? (caddr expr))
                                             (equal? 'cons (car (caddr expr)))
                                             (null? (caddr (caddr expr))))
                                        (let* ([var (cadr expr)]
                                               [other-val (cadr (caddr expr))]
                                               [type (hash-table-ref (state->var-type-map state) var)])
                                          `(= ,var (cons ,other-val (as nil ,type))))]
                                       [else `(,(if (null? (car expr)) 
                                                  'nil 
                                                  (convert-null (car expr))) . 
                                                ,(convert-null (cdr expr)))])]
                   [else expr]))
           (define (convert-boolean-literals expr)
             (cond [(null? expr) '()]
                   [(pair? expr) `(,(convert-boolean-literals (car expr)) . ,(convert-boolean-literals (cdr expr)))]
                   [(boolean? expr) (if expr 'true 'false)]
                   [else expr]))
           (define (convert-negative-numbers expr)
             (cond [(null? expr) '()]
                   [(pair? expr) `(,(convert-negative-numbers (car expr)) . ,(convert-negative-numbers (cdr expr)))]
                   [(number? expr) (if (< expr 0)
                                     `(- ,(- expr))
                                     expr)]
                   [else expr]))
           (let* ([stmts (convert-null (convert-negative-numbers (convert-boolean-literals (state->stmts state))))]
                  [postprocessed-extra-stmts (convert-null (convert-negative-numbers (convert-boolean-literals extra-stmts)))]
                  [decls (var-type-map->declarations (hash-table->alist (state->var-type-map state)))]
                  ;; [void (pretty-print (hash-table->alist (state->var-type-map state)))]
                  [no-recursion-constraint (map (lambda (var)
                                                  `(assert (= ,var false)))
                                                (filter (lambda (var)
                                                          (equal? "R" (substring (symbol->string var) 0 1)))
                                                        (map car (hash-table->alist (state->var-type-map state)))))]
                  [header `((declare-datatypes (T) ((Lst nil (cons (car T) (cdr Lst))))))]
                  [z3-stmts `(,@header ,@decls ,@stmts ,@no-recursion-constraint ,@postprocessed-extra-stmts (check-sat) (get-model))])
             z3-stmts))

         (define (check-state state extra-stmts)
           (let* ([z3-result (run-z3 (state->nonrec-model-finder state extra-stmts))]
                  [sat? (equal? 'sat (car z3-result))])
             (if sat?
               (z3-result->assignment (cdr (cadr z3-result)))
               'unsat)))

         ;; next step: advance the state

         (define (advance-state! state)
           (let* ([deletion-thunks (state->deletion-thunks state)]
                  [continue-thunks (state->continue-thunks state)]
                  [void ((car deletion-thunks))]
                  [void ((car continue-thunks))]
                  [next-state ((state->refresh state))])
             next-state))

         (define (smt-solve max-depth program constraint)
           (define body `(assert ,program ,constraint))
           (define labeled-body (label-transform body))
           (define labeled-env
             (map (lambda (v-e) `(,(car v-e) . ,(if (procedure? (cdr v-e)) (cdr v-e)
                                                  (label-transform (cdr v-e))))) default-env))

           (define initial-state (smt-evaluator labeled-body labeled-env '(top)))

           (define (search max-depth initial-state)
             ;; Interface to state functions
             (define (state->smt-result state extra-stmts)
               (check-state state extra-stmts))
             (define (sat? result)
               (not (equal? 'unsat result)))
             (define (fully-expanded? state)
               ;; condition: no recursion variables
               (all (lambda (var) (not (equal? "R" (substring (symbol->string var) 0 1))))
                    (map car (hash-table->alist (state->var-val-map state)))))
             (define (expand state)
               (advance-state! state))

             (define (find-further-solutions state sols)
               (define (ineq-stmt var val)
                 `(assert (not (= ,var ,val))))
               (let* ([next-result (state->smt-result state (map (lambda (sol)
                                                                   (let* ([var (car sol)]
                                                                          [val (cadr sol)])
                                                                     (ineq-stmt var val)))
                                                                 sols))])
                 (if (sat? next-result)
                   (let* ([sol (assoc (car (state->final state)) next-result)])
                     (pretty-print sol)
                     (cons sol (find-further-solutions state (cons sol sols))))
                   '())))


             (define (loop curr-depth state)
               (if (> curr-depth max-depth)
                 'unknown
                 (let* ([solve-result (state->smt-result state '())])
                   (if (sat? solve-result)
                     state
                     ;; (let* ([next-sol (assoc (car (state->final state)) solve-result)])
                       ;; (cons next-sol solve-result))
                       ;; state)
                     ;; (cons next-sol ;; `(assignment: ;; ,solve-result) (find-further-solutions state (list next-sol))))
                     (loop (+ curr-depth 1)
                           (expand state))))))
             (loop 0 initial-state))

           (search max-depth initial-state))

         (define (run-smt program)
           (define labeled-body (label-transform program))
           (define labeled-env
             (map (lambda (v-e) `(,(car v-e) . ,(if (procedure? (cdr v-e)) (cdr v-e)
                                                  (label-transform (cdr v-e))))) default-env))
           (let* ([state (smt-evaluator labeled-body labeled-env '(top))])
             (list state (check-state state '()))))

         (define (run-state-with-assignment max-search-depth assignment state)

           ;; step 1. add the asn as constraints to the state.
           ;; step 2. run the smt solver.
           ;; step 3. if this is unsat when the recursion variable is true, unroll (call continue thunks), up to max-search-depth, until sat.

           (define assignment-constraint 
             (map (lambda (var-val-type)
                    (let* ([var (car var-val-type)]
                           [val (cadr var-val-type)])
                      `(assert (= ,var ,val))))
                  assignment))

           (define (sat? result)
             (not (equal? 'unsat result)))

           (define (loop curr-depth state)
             (if (> curr-depth max-search-depth)
               'unknown
               (let* ([solve-result (check-state state assignment-constraint)])
                 (if (sat? solve-result)
                   (list state solve-result)
                   (loop (+ curr-depth 1)
                         (advance-state! state))))))

           (loop 0 state))

         ;; what we want to go on behind the scenes here, is a gradually growing SMT formula that encompasses all possible executions,
         ;; which acts like a huge fixed-universe model.

         ;; mcmc-state: (State, Assignment, Score)
         (define (make-mcmc-state state assignment score)
           (list state assignment score))

         (define (mcmc-state->prog-state state) (car state))
         (define (mcmc-state->assignment state) (cadr state))
         ;; scoring placeholder
         (define (mcmc-state->score state) 0.0)


         (define (exists-var? s) (equal? "E" (substring (symbol->string s) 0 1)))

         (define (formula->xrp-domains formula)
           (define (exists-implication->xrp-domain impl)
             (let* ([disj (caddr impl)]
                    [xrp-val-constraints (cdr disj)]
                    [xrp-var (cadr (car xrp-val-constraints))])
               (cons xrp-var (map caddr xrp-val-constraints))))
           (define (exists-implication? assert-stmt)
             (let* ([body (cadr assert-stmt)])
               (and (list? body)
                    (equal? '=> (car body))
                    (exists-var? (cadr body)))))
           (define (assert->exists-implication assert)
             (cadr assert))

           (map exists-implication->xrp-domain
                (map assert->exists-implication 
                     (filter exists-implication? formula))))

         ;; Returns new assignment constraint represnting a perturbed variable.
         ;; Constrains all other currently-existing variables to be the same.
         (define (perturb-assignment assignment xrp-domains)

           (define (exist-var->xrp-var v)
             (let* ([var-idx (substring
                               (symbol->string v)
                               1 (string-length (symbol->string v)))])
               (string->symbol
                 (string-append "X" var-idx))))

           (let* ([existence-variables (filter cadr (filter (lambda (a) (exists-var? (car a))) assignment))]
                  [existing-xrps (map exist-var->xrp-var (map car existence-variables))]
                  ;; [void (pretty-print `(existing-xrps ,existing-xrps ,xrp-domains))]
                  [proposal-var (uniform-select existing-xrps)]
                  [proposal-val (uniform-select (cdr (assoc proposal-var xrp-domains)))]
                  ;; [void (pretty-print `(proposal-var-val ,proposal-var ,proposal-val))]
                  [proposal-type (caddr (assoc proposal-var assignment))]
                  [assignment (cons `(,proposal-var ,proposal-val ,proposal-type)
                                    (map (lambda (assignment)
                                           (let* ([var (car assignment)]
                                                  [current-val (cadr assignment)]
                                                  [current-type (caddr assignment)])
                                             `(,var ,current-val ,current-type)))
                                         (map (lambda (xrp-var)
                                                (assoc xrp-var assignment))
                                              (filter (lambda (xrp-var)
                                                        (not (equal? proposal-var xrp-var)))
                                                      existing-xrps))))])
             assignment))

         ;; Returns new assignment constraint represnting a perturbed variable.
         ;; May set other variables.
         (define (block-perturb-assignment assignment xrp-domains)

           (define (exist-var->xrp-var v)
             (let* ([var-idx (substring
                               (symbol->string v)
                               1 (string-length (symbol->string v)))])
               (string->symbol
                 (string-append "X" var-idx))))

           (let* ([existence-variables (filter cadr (filter (lambda (a) (exists-var? (car a))) assignment))]
                  [existing-xrps (map exist-var->xrp-var (map car existence-variables))]
                  ;; [void (pretty-print `(existing-xrps ,existing-xrps ,xrp-domains))]
                  [proposal-var (uniform-select existing-xrps)]
                  [proposal-val (uniform-select (cdr (assoc proposal-var xrp-domains)))]
                  ;; [void (pretty-print `(proposal-var-val ,proposal-var ,proposal-val))]
                  [proposal-type (caddr (assoc proposal-var assignment))]
                  [assignment (list `(,proposal-var ,proposal-val ,proposal-type))])
             assignment))

         (define (proposal max-search-depth mcmc-state)
           (let* ([formula (state->stmts (mcmc-state->prog-state mcmc-state))]
                  [current-assignment (mcmc-state->assignment mcmc-state)]
                  [domains (formula->xrp-domains formula)]
                  [new-assignment (block-perturb-assignment current-assignment domains)]
                  [new-prog-state+consistent-assignment (run-state-with-assignment max-search-depth new-assignment (mcmc-state->prog-state mcmc-state))])
             (if (equal? 'unknown new-prog-state+consistent-assignment)
               mcmc-state
               (let* ([new-prog-state (car new-prog-state+consistent-assignment)]
                      [final-assignment (cadr new-prog-state+consistent-assignment)])
                 (make-mcmc-state new-prog-state 
                                  final-assignment
                                  (mcmc-state->score mcmc-state))))))

         (define (smt-mh-loop num-iter max-search-depth initial-state)
           (define samples '())

           (define (accumulate-sample! mcmc-state)
             (let* ([sample-val (cadr (assoc (car (state->final (mcmc-state->prog-state mcmc-state)))
                                             (mcmc-state->assignment mcmc-state)))]
                    [final-sample-val (if (pair? sample-val)
                                        (eval `(let ()
                                                 (define nil '())
                                                 (define Int '())
                                                 (define (Lst . xs) '())
                                                 (define (as . xs) (car xs))
                                                 (define answer ,sample-val)
                                                 answer)
                                              (environment '(rnrs))))])
               (pretty-print final-sample-val)
               (set! samples (cons final-sample-val samples))))


           (define (loop iter curr-state)
             (accumulate-sample! curr-state)
             (if (< iter num-iter)
               (let* ([score-before (mcmc-state->score curr-state)]
                      [next-state (proposal max-search-depth curr-state)]
                      [score-after (mcmc-state->score next-state)]
                      [accept? (< (log (random-real)) (- score-after score-before))])
                 (if accept?
                   (loop (+ 1 iter) next-state)
                   (loop (+ 1 iter) curr-state)))
                 curr-state))

           (loop 0 initial-state)
           samples)

         (define (smt-mh-query num-samples max-search-depth program constraint)
           (define body `(assert ,program ,constraint))
           (define labeled-body (label-transform body))
           (define labeled-env
             (map (lambda (v-e) `(,(car v-e) . ,(if (procedure? (cdr v-e)) (cdr v-e)
                                                  (label-transform (cdr v-e))))) default-env))

           (define initial-prog-state (smt-solve max-search-depth program constraint))
           (define initial-assignment (check-state initial-prog-state '()))
           (define initial-score 0.0)

           (define initial-mcmc-state (make-mcmc-state initial-prog-state initial-assignment initial-score))

           (smt-mh-loop num-samples max-search-depth initial-mcmc-state))


         )
