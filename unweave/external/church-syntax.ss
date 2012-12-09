#!r6rs

(library

 (unweave external church-syntax)

 (export var?
         var<?
         ref?
         ref->lab
         ref->var
         explode-ref
         lambda?
         lambda<?
         lambda->lab
         lambda->formals
         lambda->call
         lambda->return-type
         exp<?
         has-type-annotation?
         explode-lambda
         closure?
         factor-closure?
         closure->lambda
         closure->env
         explode-closure
         call?
         call->lab
         call->fun
         call->args
         explode-call
         primop?
         primop->lab
         primop->fun
         primop->args
         explode-primop
         if?
         if->lab
         if->cond
         if->then
         if->else
         explode-if
         letrec?
         letrec->lab
         letrec->bindings
         letrec->body
         explode-letrec
         xrp?
         xrp->lab
         xrp->scorer
         xrp->name
         xrp->prop-fx-name
         xrp->params
         explode-xrp
         xrps?
         xrps->lab
         xrps->scorer
         xrps->name
         xrps->prop-fx-name
         xrps->params
         explode-xrps
         xrp+init?
         xrp+init->lab
         xrp+init->scorer
         xrp+init->name
         xrp+init->prop-fx-name
         xrp+init->initval
         xrp+init->params
         explode-xrp+init
         factor?
         factor->lab
         factor->formals
         factor->call
         explode-factor
         const?
         const->lab
         const->val
         explode-const
         rv?
         rv->addr
         rv->name
         rv->params
         rv->val
         assert?
         assert->lab
         assert->prog
         assert->query

         explode-assert
         fundep?
         fundep->lab
         fundep->x
         fundep->y
         make-xrp-trace
         xrp-trace->addr
         xrp-trace->var
         xrp-trace->prop-fx-name
         xrp-trace->params
         xrp-trace->val
         xrp-trace->score-fx-name
         explode-xrp-trace
         quoted?
         all?
         my-any
         extend
         lookup not-found?
         subexpr-walk
         contains?
         get-mean
         get-var
         elems-after-n
         sort
         map-enumerate)

 (import (except (rnrs) string-hash string-ci-hash))

 ;; Using primitives from Matt Might's k-CFA Scheme impl

 ;; Variables ===================================================================

 (define (var? exp) (symbol? exp))
 (define (var<? v1 v2) (string<? (symbol->string v1) (symbol->string v2)))

 (define (ref? exp) (and (pair? exp) (eq? (car exp) 'ref)))
 (define (ref->lab exp) (cadr exp))
 (define (ref->var exp) (caddr exp))

 (define (explode-ref r k)
   (k (ref->lab r)
      (ref->var r)))

 ;; Lambda ======================================================================

 (define (lambda? exp) (and (pair? exp) (eq? (car exp) 'lambda)))
 (define (lambda<? lam1 lam2) (< (lambda->lab lam1) (lambda->lab lam2)))
 (define (lambda->lab exp) (cadr exp))
 (define (lambda->formals exp) (caddr exp))
 (define (lambda->call exp) (cadddr exp))
 (define (lambda->return-type exp) (car (cddddr exp)))
 (define (has-type-annotation? exp) (not (null? (cddddr exp))))

 (define (exp<? exp1 exp2)
   (cond
    ((and (var? exp1) (var? exp2))       (var<? exp1 exp2))
    ((var? exp1)                         #t)
    ((and (lambda? exp1) (lambda? exp2)) (lambda<? exp1 exp2))
    ((lambda? exp1)                      #t)
    (else                                (error "Can't compare expressions."))))

 (define (explode-lambda lm k)
   (k (lambda->lab lm)
      (lambda->formals lm)
      (lambda->call lm)))

 (define (closure? exp) (and (pair? exp) (eq? (car exp) 'closure)))
 (define (factor-closure? exp) (and (pair? exp) (eq? (car exp) 'factor-closure)))
 (define closure->lambda cadr)
 (define closure->env caddr)
 (define (explode-closure c k)
   (k (cadr c) (caddr c)))

 ;; Application =================================================================

 (define (call? term) (and (pair? term) (eq? (car term) 'call)))
 (define (call->lab call) (cadr call))
 (define (call->fun call) (caddr call))
 (define (call->args call) (cdddr call))

 (define (explode-call call k)
   (k (call->lab call)
      (call->fun call)
      (call->args call)))

 ;; Primop ======================================================================

 (define (primop? term) (and (pair? term) (eq? (car term) 'primop)))
 (define (primop->lab call) (cadr call))
 (define (primop->fun call) (caddr call))
 (define (primop->args call) (cdddr call))

 (define (explode-primop call k)
   (k (primop->lab call)
      (primop->fun call)
      (primop->args call)))

 ;; If ==========================================================================

 (define (if? term) (and (pair? term) (eq? (car term) 'if)))
 (define (if->lab call) (cadr call))
 (define (if->cond call) (caddr call))
 (define (if->then call) (cadddr call))
 (define (if->else call) (cadddr (cdr call)))

 (define (explode-if ifte k)
   (k (if->lab ifte)
      (if->cond ifte)
      (if->then ifte)
      (if->else ifte)))

 ;; Letrec ======================================================================

 (define (letrec? term) (and (pair? term) (eq? (car term) 'letrec)))
 (define (letrec->lab call) (cadr call))
 (define (letrec->bindings call) (caddr call))
 (define (letrec->body call) (cadddr call))

 (define (explode-letrec lrc k)
   (k (letrec->lab lrc)
      (letrec->bindings lrc)
      (letrec->body lrc)))

 ;; Random primitives============================================================
 ;; Random primitives============================================================

 (define (xrp? term)
   (and (pair? term) (eq? (car term) 'xrp)))

 (define (xrp->lab call) (cadr call))
 (define (xrp->scorer call) (caddr call))
 (define (xrp->name call) (cadddr call))
 (define (xrp->prop-fx-name call) (cadddr (cdr call)))
 (define (xrp->params call) (cddddr (cdr call)))

 (define (explode-xrp x k)
   (k (xrp->lab x)
      (xrp->scorer x)
      (xrp->name x)
      (xrp->prop-fx-name x)
      (xrp->params x)))

 (define (xrps? term)
   (and (pair? term) (eq? (car term) 'xrps)))

 (define (xrps->lab call) (cadr call))
 (define (xrps->scorer call) (caddr call))
 (define (xrps->name call) (cadddr call))
 (define (xrps->prop-fx-name call) (cadddr (cdr call)))
 (define (xrps->params call) (cddddr (cdr call)))

 (define (explode-xrps x k)
   (k (xrps->lab x)
      (xrps->scorer x)
      (xrps->name x)
      (xrp->prop-fx-name x)
      (xrps->params x)))

 (define (xrp+init? term)
   (and (pair? term) (eq? (car term) 'xrp+init)))

 (define (xrp+init->lab call) (cadr call))
 (define (xrp+init->scorer call) (caddr call))
 (define (xrp+init->name call) (cadddr call))
 (define (xrp+init->prop-fx-name call) (cadddr (cdr call)))
 (define (xrp+init->initval call) (car (cddddr (cdr call))))
 (define (xrp+init->params call) (cddddr (cddr call)))

 (define (explode-xrp+init x k)
   (k (xrp+init->lab x)
      (xrp+init->scorer x)
      (xrp+init->name x)
      (xrp+init->prop-fx-name x)
      (xrp+init->initval x)
      (xrp+init->params x)))

 (define (factor? term)
   (and (pair? term) (eq? (car term) 'factor)))

 (define factor->lab cadr)
 (define factor->formals caddr)
 (define factor->call cadddr)

 (define (explode-factor x k)
   (k (lambda->lab x) (lambda->formals x) (lambda->call x)))

 ;; Constants====================================================================

 (define (const? t) (and (pair? t) (eq? (car t) 'const)))

 (define const->lab cadr)
 (define const->val caddr)

 (define (explode-const x k)
   (k (const->lab x) (const->val x)))

 ;; Random variable==============================================================

 (define (rv? term)
   (and (pair? term) (eq? (car term) 'rv)))

 (define (rv->addr r) (list-ref r 1))
 (define (rv->name r) (list-ref r 3))
 (define (rv->params r) (list-ref r 4))
 (define (rv->val r) (list-ref r 5))

 (define (make-xrp-trace addr var prop-fx-name params val score-fx-name)
   `(rv ,addr ,var ,prop-fx-name ,params ,val ,score-fx-name))
 (define (xrp-trace->addr t) (list-ref t 0))
 (define (xrp-trace->var t) (list-ref t 1))
 (define (xrp-trace->prop-fx-name t) (list-ref t 2))
 (define (xrp-trace->params t) (list-ref t 3))
 (define (xrp-trace->val t) (list-ref t 4))
 (define (xrp-trace->score-fx-name t) (list-ref t 5))
 (define (explode-xrp-trace x k)
   (apply k (cdr x)))

 ;; Asserts

 (define (explode-assert x k)
   (apply k (cdr x)))
 (define (assert? e) (and (pair? e) (eq? 'assert (car e))))
 (define (assert->lab e) (cadr e))
 (define (assert->prog e) (caddr e))
 (define (assert->query e) (cadddr e))

 ;; Functional dependencies

 (define (fundep? e) (and (pair? e) (eq? 'fundep (car e))))
 (define (fundep->lab e) (cadr e))
 (define (fundep->x e) (caddr e))
 (define (fundep->y e) (cadddr e))

 ;; Quoted values================================================================

 (define (quoted? e) (and (pair? e) (eq? 'quote (car e))))

 ;; Data structures, utility functions===========================================

 ;; Boolean functions

 (define (all? p xs)
   (cond [(null? xs) #t]
         [else (if (not (p (car xs))) #f (all? p (cdr xs)))]))

 (define (my-any p xs)
   (cond [(null? xs) #f]
         [else (if (p (car xs)) #t (my-any p (cdr xs)))]))

 ;; Contexts

 (define (extend cxt label val)
   (cons (cons label val) cxt))

 (define (lookup cxt label)
   (let* ([lk (assoc label cxt)])
     (if lk (cdr lk) 'not-found)))

 (define (not-found? x) (equal? x 'not-found))


 ;; Subexpressions


 (define (subexpr-walk f expr)
   (cond [(null? expr) expr]
         [(list? expr) (let* ([new-expr (f expr)])
                         (cond [(list? new-expr)
                                (cons (subexpr-walk f (car new-expr))
                                      (subexpr-walk f (cdr new-expr)))]
                               [else new-expr]))]
         [else expr]))

 ;; List containment

 (define (contains? i l)
   (if (null? l) #f
       (or (equal? (car l) i)
           (contains? i (cdr l)))))


 (define (get-mean vals)
   (/ (apply + (map (lambda (s) s) vals)) (length vals)))

 (define (get-var vals)
   (let* ([mean (get-mean vals)])
     (/ (apply + (map (lambda (s) (* (- mean s) (- mean s))) vals)) (length vals))
     ))

 (define (elems-after-n elems n)
   (if (= n 0)
       elems
       (elems-after-n (cdr elems) (- n 1))
       ))

 (define (sort cmp xs)
   (if (null? xs)
       '()
       (let*-values ([(pivot) (car xs)]
                     [(lt gt) (partition (lambda (x) (cmp x pivot)) (cdr xs))])
         (append (sort cmp lt) (list pivot) (sort cmp gt)))))

 ;; Enumeration

 (define (map-enumerate f xs)
   (define (loop f xs i)
     (if (null? xs) '()
         (cons (f (car xs) i) (loop f (cdr xs) (+ i 1)))))
   (loop f xs 0))

 )
