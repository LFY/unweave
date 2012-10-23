(import (rnrs)
        (_srfi :1)
        (srfi :27)
        (delimcc-simple-ikarus)
        (printing)
        (only (ikarus) fork waitpid)
        (only (scheme-tools) system))

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
        [else (equal? a e)]))

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

  (define recur-ctr 0)
  (define (next-recur)
    (let* ([res (string->symbol (string-append "Y" (number->string recur-ctr)))])
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
                  [y (next-recur)]
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

  (E tree (V #t))
  (let* ([ordered-stmts (reverse stmts)]
         [declares (filter (lambda (x) (equal? (car x) 'declare-const))
                           ordered-stmts)]
         [asserts (filter (lambda (x) (equal? (car x) 'assert))
                          ordered-stmts)])
    (append declares asserts)))


;; Our language: Constructive expressions with external lambda, control flow

(define (geometric-gen)
  (if (dist #t 0.5 #f 0.5)
     0
     `(+ 1 ,(lambda () (geometric-gen)))))

(define initial-tree (reify (lambda () (geometric-gen))))

;; we need an odd number here?

;; (define unfold5 (pv-unfold-by 9 initial-tree))
;; 
;; (pretty-print unfold5)
;; 
;; (for-each pretty-print 
;;           (unfolded-tree->formula unfold5))

;; TODO: 
;; 1. some way to communicate with Z3, obtain assignments, findall, etc.

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
  (define (gen-z3-file) (string-append "constr_" (new-file-id) ".ss"))
  (define (gen-output-file) (string-append "output_" (new-file-id) ".ss"))
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
      (list sat-unsat assignment-expr))))

(pretty-print (run-z3
  '((declare-const X0 Bool)
    (declare-const B0 Bool)
    (declare-const Y0 Int)
    (declare-const X1 Bool)
    (declare-const B2 Bool)
    (declare-const Y1 Int)
    (declare-const X2 Bool)
    (declare-const B4 Bool)
    (declare-const Y2 Int)
    (declare-const X3 Bool)
    (declare-const B6 Bool)
    (declare-const Y3 Int)
    (declare-const X4 Bool)
    (declare-const B8 Bool)
    (declare-const Y4 Int)
    (declare-const Y5 Int)
    (declare-const V4 Int)
    (declare-const B9 Bool)
    (declare-const V3 Int)
    (declare-const B7 Bool)
    (declare-const V2 Int)
    (declare-const B5 Bool)
    (declare-const V1 Int)
    (declare-const B3 Bool)
    (declare-const V0 Int)
    (declare-const B1 Bool)
    (assert (=> true (or (= X0 true) (= X0 false))))
    (assert (= B0 (= X0 true)))
    (assert (=> B0 (= Y0 0)))
    (assert (=> B1 (or (= X1 true) (= X1 false))))
    (assert (= B2 (= X1 true)))
    (assert (=> B2 (= Y1 0)))
    (assert (=> B3 (or (= X2 true) (= X2 false))))
    (assert (= B4 (= X2 true)))
    (assert (=> B4 (= Y2 0)))
    (assert (=> B5 (or (= X3 true) (= X3 false))))
    (assert (= B6 (= X3 true)))
    (assert (=> B6 (= Y3 0)))
    (assert (=> B7 (or (= X4 true) (= X4 false))))
    (assert (= B8 (= X4 true)))
    (assert (=> B8 (= Y4 0)))
    (assert (=> B9 (= V4 (+ 1 Y5))))
    (assert (= B9 (= X4 false)))
    (assert (=> B9 (= Y4 V4)))
    (assert (xor B9 B8))
    (assert (=> B7 (= V3 (+ 1 Y4))))
    (assert (= B7 (= X3 false)))
    (assert (=> B7 (= Y3 V3)))
    (assert (xor B7 B6))
    (assert (=> B5 (= V2 (+ 1 Y3))))
    (assert (= B5 (= X2 false)))
    (assert (=> B5 (= Y2 V2)))
    (assert (xor B5 B4))
    (assert (=> B3 (= V1 (+ 1 Y2))))
    (assert (= B3 (= X1 false)))
    (assert (=> B3 (= Y1 V1)))
    (assert (xor B3 B2))
    (assert (=> B1 (= V0 (+ 1 Y1))))
    (assert (= B1 (= X0 false)))
    (assert (=> B1 (= Y0 V0)))
    (assert (xor B1 B0))

    (check-sat)
    (get-model))))

;; 2. hook up query statements properly (Y0 == Result)
;; 3. source translation to the lazy trace-generating code (geometric-gen)
;; 4. test uninterpreted functions, lists
