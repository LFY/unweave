#!r6rs
(library (unweave smt-search)
         (export smt-solve
                 run-smt)

         (import (rnrs)
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
           (define continue-thunks '())
           (define deletion-thunks '())

           (define symbol-maker-map (make-hash-table equal?))

           (define addr-var-map (make-hash-table equal?))

           (define var-val-map (make-hash-table equal?))
           (define var-type-map (make-hash-table equal?))
           (define lazy-map (make-hash-table equal?))

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
                                                 (equal? "Y" (substring (symbol->string v) 0 1)))))

           (define (inst-type! var val)
             (hash-table-set! var-type-map var val))

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
                                          (pretty-print `(unknown! ,val))
                                          'UNKNOWN-TYPE)])])
               (pretty-print `(val->type ,val ,result))
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

           (define (next-recursion-flag addr) (addr->var addr 'R))

           (define (add-stmt-once! stmt) (if (not (member stmt stmts)) (add-stmt! stmt) '()))
           (define (add-stmt! stmt) (set! stmts (cons stmt stmts)))
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
             (pretty-print `(infer ,prim ,@var-vals))
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
                                            (pretty-print `(inst-type! ,rest-var-val ,type))
                                            (inst-type! rest-var-val type)
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
                             (pretty-print `(unknown: (,prim ,@var-vals)))
                             'UNKNOWN-TYPE)])))

           (define (convert-prim f args)
             (if (equal? 'null? f) 
               `(= nil ,@args)
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
                                              (pretty-print `(inst-type! ,Rv (if ,eval-T? ,(get-type Tv) ,(get-type Ev))))
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
               [(assert? ex) (explode-assert ex (lambda (l b)
                                                  (let* ([Av (next-assert addr)]
                                                         [Bv (E b env (cons l addr) lazy? control-env)])
                                                    (inst-type! Av 'Bool)
                                                    (add-stmt!  `(assert (and (= ,Av ,Bv) (= ,Av #t))))
                                                    Bv)))]
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
                                                (pretty-print `(call ,Vv ,f ,vals))
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
                                                                                       (set! deletion-thunks
                                                                                         (cons
                                                                                           (lambda ()
                                                                                             (set-car! (cdr recursion-condition) #t)
                                                                                             (set-car! (cdr recursion-definition) #t))
                                                                                           deletion-thunks))
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
                                                             (pretty-print `(proc-lazy ,Vv ,(ref->var f) ,@vals))
                                                             ;; type inference is needed here (for primitive functions)
                                                             (inst-type! Vv (infer-return-type (ref->var f) vals))
                                                             Vv)
                                                           (begin
                                                             (pretty-print `(proc-eager ,Vv ,(ref->var f) ,@vals))
                                                             (inst-type! Vv (infer-return-type (ref->var f) vals))
                                                             (if (all (lambda (x) (not (lazy-var? x)))
                                                                      vals)
                                                               (inst-val-type! Vv (apply proc (map (lambda (v) (if (var? v) (get-val v) v))
                                                                                                   vals))))
                                                             Vv)))]
                                                      [else (pretty-print `(error-in-call-norm-eval ,proc))]))))]
               [(ref? ex) (let* ([lookup-res (lookup env (ref->var ex))])
                            (if (not-found? lookup-res) 
                              (begin
                                (pretty-print `(not-found: ,lookup-res ,(ref->var ex)))
                                (cond [(rv? lookup-res)
                                       (list-ref lookup-res 5)]
                                      [else lookup-res]))
                              lookup-res))]
               [(xrp? ex) (explode-xrp ex (lambda (lab scorer name prop-fx-name params)
                                            (let* ([Xv (next-choice (cons lab addr))]
                                                   [Ev (next-choice-existence (cons lab addr))]
                                                   [param-vals (map (lambda (p) (E p env addr lazy? control-env)) params)]) 
                                              (inst-type! Ev 'Bool)
                                              (add-stmt! `(assert (= ,Ev ,(if (null? control-env) #t
                                                                            `(and ,@(map (lambda (var-val)
                                                                                           `(= ,(car var-val) ,(cdr var-val)))
                                                                                         control-env))))))
                                              (add-stmt! `(assert (=> ,Ev (or ,@(map (lambda (v) `(= ,Xv ,v)) param-vals)))))
                                              ;; just do a uniform selection for now
                                              (inst-val-type! Xv (uniform-select param-vals))
                                              Xv)))]
               [(const? ex) (explode-const ex (lambda (lab c) (if (null? c) '() c)))]
               [else ex]))
           (let* ([final-var (E ex env addr #f '())])
             (letrec ([refresh-state (lambda () 
                                       (make-state final-var var-val-map var-type-map lazy-map continue-thunks deletion-thunks stmts refresh-state))])
               (refresh-state))))

         (define (make-state 
                   final-var 
                   var-val-map 
                   var-type-map 
                   lazy-map 
                   continue-thunks 
                   deletion-thunks 
                   stmts
                   refresh-state)
           `(,final-var ,var-val-map ,var-type-map ,lazy-map ,continue-thunks ,deletion-thunks ,stmts ,refresh-state))

         (define (make-list-ref n)
           (lambda (xs) (list-ref xs n)))

         (define state->final-var (make-list-ref 0))
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

         (define (state->nonrec-model-finder state)
           (define (convert-null expr)
             (cond [(null? expr) '()]
                   [(pair? expr) `(,(if (null? (car expr)) 'nil
                                      (convert-null (car expr))) . ,(convert-null (cdr expr)))]
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
                  [decls (var-type-map->declarations (hash-table->alist (state->var-type-map state)))]
                  [no-recursion-constraint (map (lambda (var)
                                                  `(assert (= ,var false)))
                                                (filter (lambda (var)
                                                          (equal? "R" (substring (symbol->string var) 0 1)))
                                                        (map car (hash-table->alist (state->var-type-map state)))))]
                  [header `(
                            (declare-datatypes (T) ((Lst nil (cons (car T) (cdr Lst)))))
                            )]
                  [z3-stmts `(,@header ,@decls ,@stmts ,@no-recursion-constraint (check-sat) (get-model))])
             z3-stmts))

         (define (check-state state)
           (let* ([z3-result (run-z3 (state->nonrec-model-finder state))]
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
           (define body `(assert (,constraint ,program)))
           (define labeled-body (label-transform body))
           (define labeled-env
             (map (lambda (v-e) `(,(car v-e) . ,(if (procedure? (cdr v-e)) (cdr v-e)
                                                  (label-transform (cdr v-e))))) default-env))

           (define initial-state (smt-evaluator labeled-body labeled-env '(top)))

           (define (search max-depth initial-state)
             ;; Interface to state functions
             (define (state->smt-result state)
               (check-state state))
             (define (sat? result)
               (not (equal? 'unsat result)))
             (define (fully-expanded? state)
               ;; condition: no recursion variables
               (all (lambda (var) (not (equal? "R" (substring (symbol->string var) 0 1))))
                    (map car (hash-table->alist (state->var-val-map state)))))
             (define (expand state)
               (advance-state! state))

             (define (loop curr-depth state)
               (if (> curr-depth max-depth)
                 'unknown
                 (let* ([solve-result (state->smt-result state)])
                   (if (sat? solve-result)
                     solve-result
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
             (list state (check-state state))))

         )
