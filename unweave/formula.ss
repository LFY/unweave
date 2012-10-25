#!r6rs

;; Converts an unfolded trace/search tree to a formula.

(library

 (unweave formula)

 (export unfolded-tree->formula)

 (import (rnrs)
         (unweave probability-tree)
         (only (scheme-tools) symbol-maker))

 (define (unfolded-tree->formula tree)

   (define stmts '())

   (define next-control (symbol-maker 'C))
   (define next-ret (symbol-maker 'Y))
   (define next-recur (symbol-maker 'R))
   (define next-var (symbol-maker 'X))
   (define next-branch-var (symbol-maker 'B))
   (define next-det-var (symbol-maker 'V))

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

 )