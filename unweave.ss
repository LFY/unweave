(import (rnrs)
        (scheme-tools srfi-compat :1)
        (srfi :27)
        (delimcc-simple-ikarus)
        (only (ikarus) fork waitpid)
        (only (scheme-tools) system pretty-print))

;; Unweave: Probabilistic Programming with Constraint Solving

;; Based on HANSEI (begin Hansei duplication)

;; Random sampling primitives

(random-source-randomize! default-random-source)

(define (uniform a b)
  (+ a (* (- b a) (random-real))))

(define (randint a b)
  (+ (random-integer (+ (- b a) 1)) a))

(define (scan f z xs)
  (cond [(null? xs) `(,z)]
        [else (let* ([res (f z (car xs))])
                (cons z (scan f res (cdr xs))))]))

(define (scan1 f xs)
  (scan f (car xs) (cdr xs)))

(define (rnd-select pvs)
  (cond [(null? pvs) '()]
        [else
         (letrec* ([smp (uniform 0 1)]
                   [pvs* (zip (scan1 + (map car pvs)) pvs)]
                   [iterator (lambda (pvs)
                               (let* ([pv (car pvs)]
                                      [p (car pv)]
                                      [v (cadr pv)])
                                 (cond [(< smp p) v]
                                       [else (iterator (cdr pvs))])))])
                  (iterator pvs*))]))

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

;; (end Hansei duplication)

;; Enhance search tree with partial traces
;; (pv (probability continuation-thunk sample-value
;;      (trace-expr ...
;;         <thunk> ;; recursion
;;         (pv ... ;; another choice following in control flow

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


;; Converts an unfolded trace/search tree to a formula.
(define (unfolded-tree->formula tree)

  (define stmts '())

  (define control-ctr 0)
  (define (next-control)
    (let* ([res (string->symbol (string-append "C" (number->string control-ctr)))])
      (set! control-ctr (+ 1 control-ctr))
      res))

  (define ret-ctr 0)
  (define (next-ret)
    (let* ([res (string->symbol (string-append "Y" (number->string ret-ctr)))])
      (set! ret-ctr (+ 1 ret-ctr))
      res))

  (define recur-ctr 0)
  (define (next-recur)
    (let* ([res (string->symbol (string-append "R" (number->string recur-ctr)))])
      (set! recur-ctr (+ 1 recur-ctr))
      res))

  (define var-ctr 0)
  (define (next-var)
    (let* ([res (string->symbol (string-append "X" (number->string var-ctr)))])
      (set! var-ctr (+ 1 var-ctr))
      res))

  (define branch-ctr 0)
  (define (next-branch-var)
    (let* ([res (string->symbol (string-append "B" (number->string branch-ctr)))])
      (set! branch-ctr (+ 1 branch-ctr))
      res))

  (define val-ctr 0)
  (define (next-det-var)
    (let* ([res (string->symbol (string-append "V" (number->string val-ctr)))])
      (set! val-ctr (+ 1 val-ctr))
      res))

  (define (add-stmt-once! stmt)
    (if (not (member stmt stmts))
        (add-stmt! stmt)
        '()))

  (define (recur? v) (equal? "R" (substring (symbol->string v) 0 1)))

  (define (add-stmt! stmt)
    (set! stmts (cons stmt stmts)))

  (define (to-asn env)
    (map (lambda (v-e)
           `(,(car v-e) == ,(cdr v-e)))
         env))

  (define branch-envs '())

  (define (V val)
    (cond [(boolean? val) (if val 'true 'false)]
          [else val]))

  (define type-cxt '())

  (define (extend-type-cxt! entry)
    (set! type-cxt (cons entry type-cxt)))


  (define (all p xs)
    (if (null? xs) #t
        (and (p (car xs)) (all p (cdr xs)))))

  (define (some p xs)
    (if (null? xs) #f
        (or (p (car xs)) (some p (cdr xs)))))

  (define (lookup-type v)
    (cond [(and (number? v) (exact? v)) 'Int]
          [(and (number? v) (inexact? v)) 'Real]
          [(boolean? v) 'Bool]
          [(symbol? v) (let ([lookup-result (assoc v type-cxt)])
                         (if lookup-result
                             (cdr lookup-result)
                             'A))]
          [else 'A]))

  ;; type inference (FIXME: only sort of works in very limited cases)
  (define (infer-type f args)
    (let* ([arg-types (map lookup-type args)])
      (cond [(member f '(+ - * expt))
             (let* ([res-type (if (all (lambda (t) (not (equal? t 'Real))) arg-types)
                                  'Int
                                  'Real)])
               (for-each (lambda (val type)
                           (if (and (not (number? val)) (equal? 'A type))
                             (begin
                               (extend-type-cxt! (cons val res-type))
                               (add-stmt! `(declare-const ,val ,res-type)))))
                         args arg-types)
               res-type)]
            [(member f '(log exp sin cos tan)) 'Real]
            [else 'A])))

  (define (constantly y)
    (lambda (x) y))

  (define (infer-arg-types f result-type args)
    (cond [(member f '(+ - * expr))
           (if (equal? result-type 'Int)
               (map (constantly 'Int) args)
               (map (constantly 'Real) args))]
          [(member f '(log exp sin cos tan))
           (map (constantly 'Real) args)]
          [else (map (constantly 'A) args)]))

  (define (E expr control-var)
    (cond [(pv? expr)
           (let* ([v (next-var)]
                  [y (next-ret)]
                  [choices (pv->dist expr)]
                  [domain (map V (map caddr choices))]
                  [type (lookup-type (car (map caddr choices)))] ;; Type inference
                  [these-branch-vars '()])

             (extend-type-cxt! (cons v type))
             (add-stmt! `(declare-const ,v ,type))

             (add-stmt! `(assert (=> ,control-var (or ,@(map (lambda (d) `(= ,v ,d)) domain)))))
             (for-each (lambda (choice)
                         (if (null? (cdddr choice)) '()
                           (let* ([choice-val (V (caddr choice))]
                                  [branch-var (next-branch-var)]
                                  ;; choice->trace
                                  [val (E (cadddr choice) branch-var)])
                             (set! these-branch-vars (cons branch-var these-branch-vars))

                             (extend-type-cxt! (cons branch-var 'Bool))
                             (add-stmt! `(declare-const ,branch-var Bool))

                             (add-stmt! `(assert (= ,branch-var (= ,v ,choice-val))))

                             (if (not (assoc y type-cxt))
                               (begin
                                 (extend-type-cxt! (cons y (lookup-type val)))
                                 (add-stmt! `(declare-const ,y ,(lookup-type val)))))

                             (add-stmt! `(assert (=> ,branch-var (= ,y ,val))))
                             )))
                       choices)
             (if (not (null? these-branch-vars))
                 (add-stmt! `(assert (xor ,@these-branch-vars))))
             y)]
          [(procedure? expr)
           (let* ([var (next-recur)])
             var)]
          [(pair? expr)
           (let* ([v (next-det-var)]
                  [f (car expr)]
                  [vals (map (lambda (x) (E x control-var)) (cdr expr))]
                  [type-of-v (infer-type f vals)])

             (extend-type-cxt! (cons v type-of-v))
             (add-stmt! `(declare-const ,v ,type-of-v))

             (add-stmt! `(assert (=> ,control-var (= ,v (,f ,@vals)))))

             v)]
          [else (V expr)]))

  (define (format-assert assert)
    (define (loop expr)
      (cond [(null? expr) '()]
            [(pair? expr) `(,(loop (car expr)) . ,(loop (cdr expr)))]
            [(number? expr) (if (< expr 0) `(- ,(- expr)) expr)]
            [else expr]))
    `(assert ,(loop (cadr assert))))


  (E tree (V #t))
  (let* ([ordered-stmts (reverse stmts)]
         ;; FIXME: generate thing sin the correct order the first time
         [declares (filter (lambda (x) (equal? (car x) 'declare-const))
                           ordered-stmts)]
         [asserts (filter (lambda (x) (equal? (car x) 'assert))
                          ordered-stmts)]
         [formatted-asserts (map format-assert asserts)])
    (append declares formatted-asserts)))


(define (geometric-gen)
  (if (dist #t 0.5 #f 0.5)
      0
      `(+ 1 ,(lambda () (geometric-gen)))))

(define (model)
  (if (dist #t 0.5 #f 0.5)
    (lambda () (f))
    (dist 3 0.5 4 0.5)))

(define (f)
  (dist 1 0.5 2 0.5))

(define (g)
  (dist 3 0.5 4 0.5))

(define initial-tree (reify (lambda () (geometric-gen))))

;; we need an odd number here?

(define unfold5 (pv-unfold-by 2 initial-tree))
(define test-formula (unfolded-tree->formula unfold5))

(pretty-print unfold5)
(for-each pretty-print test-formula)

;; Communicating with Z3 (todo: FFI?)
;; return value: an environment of assignments or #f (unsat)
;; Creating temporary files

(define (new-file-id)
  (fork
    (lambda (child-pid)
      (let* ([status (waitpid child-pid)])
        (number->string child-pid)))
    (lambda () (exit))))

(define (readlines filename)
  (call-with-input-file filename
    (lambda (p)
      (let loop ((line (read-line p))
                 (result '()))
        (if (eof-object? line)
            (reverse result)
            (loop (read-line p) (cons line result)))))))

(define (run-z3 stmts)
  (define (gen-z3-file) (string-append "constr_" (new-file-id) ".z3"))
  (define (gen-output-file) (string-append "output_" (new-file-id) ".z3"))
  (let ([z3-script-file (gen-z3-file)]
        [z3-output-file (gen-output-file)])
    (system (format "rm -rf ~s" z3-script-file))
    (with-output-to-file z3-script-file
                         (lambda () (for-each (lambda (x) 
                                                (display x) 
                                                (newline))
                                              stmts)))
    (system (format "z3 -smt2 ~s > ~s" 
                    z3-script-file 
                    z3-output-file))
    (let* ([lines (readlines z3-output-file)]
           [sat-unsat (string->symbol (car lines))]
           [assignment (let loop ([todo (cdr lines)]
                                  [acc ""])
                         (if (null? todo) acc
                           (loop (cdr todo) 
                                 (string-append acc (car todo)))))]
           [assignment-expr (with-input-from-string assignment read)])
      (system (format "rm ~s" z3-script-file))
      (system (format "rm ~s" z3-output-file))
      (list sat-unsat assignment-expr))))

;; (pretty-print (run-z3 (append test-formula (list '(check-sat) '(get-model)))))

;; 2. hook up query statements properly (Y0 == Result)

;; Introducing query/constraint statements
;; query: just an SMT 2.0 assert formula on the return value

(define test-query (lambda (result)
                     `(= ,result 10)))

;; Constraint solving algorithm: incremental unfolding

;; step 1. unfold model
;; step 2. collect assignments that satisfy the constraints (expressed as query stmt on the resulting sample)
;; step 3. add those assignments to the store
;; step 4. goto 1, but add that assignment to the set of forbidden states.

(define (incremental-unfold query tree)
  (define max-depth 10)
  (define models '())
  (define (loop depth curr-tree)
    (if (= depth max-depth) 'done
      (let* ([formula (unfolded-tree->formula curr-tree)]
             [model (run-z3 (append formula 
                                    (list `(assert ,(query 'Y0))
                                          '(check-sat)
                                          '(get-model))))])
        (pretty-print 'tree-and-formula)
        (pretty-print curr-tree)
        (pretty-print formula)

        (if (equal? 'sat (car model))
          (begin
            (set! models (cons model models))
            (loop (+ 1 depth) (pv-unfold (pv-unfold curr-tree))))
          (begin
            (set! models (cons 'unsat models))
            (loop (+ 1 depth) (pv-unfold (pv-unfold curr-tree))))))))
  (pretty-print tree)
  (loop 0 (pv-unfold tree))
  models)

(for-each pretty-print (incremental-unfold test-query (reify (lambda () (model)))))

;; Dealing with recursive calls.

;; 1. Treat the recursive call as an uninterpreted function symbol. This has
;; issues with probabilistic programs, since the SMT solver does not allow
;; _nondeterministic_ functions out of the box, i.e., it does not account for
;; (geometric-gen ()) != (geometric-gen ()). Not too clear how to deal with this.

;; 2. Track which function is being called at the point of recursion. Once we
;; get a satisfying assignment for our partially-unrolled trace, i.e., for the
;; constraint C1 = (= 10 (geometric-gen)):

;; (sat
;;   (model (define-fun Y0 () Int 10)
;;     (define-fun B1 () Bool true) (define-fun V0 () Int 10)
;;     (define-fun R0 () Int 9) (define-fun B0 () Bool false)
;;     (define-fun X0 () Bool false)))

;; We can augment the trace tree with information about which function is being
;; called; we use this information to associate R0 with another call
;; (geometric-gen). Now we know that in order for C1 to be true, we need C2 =
;; (= 9 (geometric-gen)) (because that was the call associated with R0). This results in a model

;; (sat
;;   (model (define-fun Y0 () Int 9)
;;     (define-fun B1 () Bool true) (define-fun V0 () Int 9)
;;     (define-fun R0 () Int 8) (define-fun B0 () Bool false)
;;     (define-fun X0 () Bool false)))

;; and so on. This seems cumbersome---it is like asking a SMT solver to do the
;; interpretation for you, then using the reply to advance the state
;; just a little bit further---but we are also allowed to expand the tree by
;; different amounts; in general, if we expand the tree by N steps, we get a
;; formula representing all possible executions N function calls away.

;; However, it is difficult to identify random variables here; it is not clear
;; how to reproduce the "database" of random variables unless there is also an
;; addressing scheme in play.

;; If our goal is to simply generate satisfying assignments with the right
;; probability, probability, however, it might not be so bad---there is no
;; database, we are just exploring forward gradually. 
 
;; Inference algorithms.

;; Look-ahead importance sampling
;; given a query stmt:
;; step 1. unfold the tree, convert to formula
;; step 2. gather satisfying assignments for the first choice, weight by probability
;; step 3. sample from that
;; step 4. pick the subtree corresponding to that choice. goto 1.


