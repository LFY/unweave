#!r6rs

(library

 (unweave external normal-interpreter)

 (export normal-evaluator
         default-env)

 (import (except (rnrs) string-hash string-ci-hash)
         (scheme-tools srfi-compat :1)
         (only (scheme-tools) pretty-print)
         (only (ikarus) modulo)
         (unweave external labeling)
         (unweave external church-syntax))

 (define (my-or a b) (or a b))
 (define (my-and . bs)
   (define (loop xs)
     (if (null? xs) #t
       (and (car xs) (loop (cdr xs)))))
   (loop bs))

 (define (my-not x) (not x))

 (define default-env
   `((+ . ,+)
     (- . ,-)
     (/ . ,/)
     (* . ,*)

     (sqrt . ,sqrt)
     (abs . ,abs)
     (null? . ,null?)
     (equal? . ,equal?)

     (= . ,=)
     (> . ,>)
     (< . ,<)
     (>= . ,>=)
     (<= . ,<=)

     (or . ,my-or)
     (and . ,my-and)
     (not . ,my-not)
     (list . ,list)
     (list-ref . ,list-ref)
     (cons . ,cons)
     (car . ,car)
     (cdr . ,cdr)
     (log . ,log)
     (exp . ,exp)
     (max . ,max)
     (modulo . ,modulo)
     (floor . ,floor)

     (display . ,display)
     (newline . ,newline)
     (pretty-print . ,pretty-print)
     (apply . ,apply)

     (map . (lambda (f xs) (if (null? xs) '() (cons (f (car xs)) (map f (cdr xs))))
               ((a b) (List a) (List b))))
     (filter . (lambda (p xs) (if (null? xs) '()
                             (if (p (car xs)) (cons (car xs) (filter p (cdr xs)))
                                 (filter p (cdr xs))))
                  ((a Bool) (List a) (List a))))
     (bigram . (lambda (xs) (if (null? (cdr xs)) '() (cons (cons (car xs)
                                                            (cons (car (cdr xs)) '())) (bigram (cdr xs))))
                  ((List a) (List (List a)))))

     (repeat . (lambda (n f) (if (= n 0) '() (cons (f) (repeat (- n 1) f)))
                  (Int (() a) (List a))))

     (zip . (lambda (xs1 xs2) (if (or (null? xs1) (null? xs2)) '() (cons
                                                               (cons (car xs1) (cons (car xs2) '()))
                                                               (zip (cdr xs1) (cdr xs2))))))
     (take . (lambda (xs n)
               (if (= n 0) '()
                   (cons (car xs) (take (cdr xs) (- n 1))))))

     (reverse . (lambda (xs)
                  (letrec
                      ([loop (lambda (acc xs)
                               (cond [(null? xs) acc]
                                     [else (loop (cons (car xs) acc) (cdr xs))]))])
                    (loop '() xs))))
     (length . (lambda (xs)
                 (if (null? xs) 0
                     (+ 1 (length (cdr xs))))
                 ((List a) Int)))

     (mirror . (lambda (xs) (letrec ([stop-site (floor ( /  (length xs) 2))]) (take (zip xs (reverse xs)) stop-site))))
     (without . (lambda (i xs)
                  (letrec ([loop2 (lambda (j todo acc)
                                    (if (= j (length xs)) acc
                                        (if (= i j)
                                            (loop2 (+ j 1) (cdr todo) acc)
                                            (loop2 (+ j 1) (cdr todo) (cons (car todo) acc)))))])
                    (loop2 0 xs '()))))

     (sum . (lambda (xs) (if (null? xs) 0 (+ (car xs) (sum (cdr xs))))))

     (append . (lambda (xs ys)
                 (if (null? xs) ys
                     (cons (car xs) (append (cdr xs) ys)))))

     (pairs . (lambda (xs)
                (cond [(null? xs) '()]
                      [(null? (cdr xs)) '()]
                      [else
                       (append (map (lambda (i) (cons (car xs) (cons i '())))
                                    (cdr xs))
                               (pairs (cdr xs)))])))

     (concat . (lambda (xss)
                 (if (null? xss) '()
                     (append (car xss) (concat (cdr xss))))))

     (cadr . (lambda (xs) (car (cdr xs))))
     (caddr . (lambda (xs) (car (cdr (cdr xs)))))
     (cadddr . (lambda (xs) (car (cdr (cdr (cdr xs))))))

     (transpose . (lambda (xss)
                    (if (null? (car xss)) '()
                        (cons (map (lambda (xs) (car xs)) xss)
                              (transpose (map (lambda (xs) (cdr xs)) xss))))))

     (assoc . (lambda (val alist)
                (if (null? alist) #f
                    (if (equal? val (car (car alist))) (car alist)
                        (assoc val (cdr alist))))))))

 (define (normal-evaluator ex env addr)
   (define (lookup cxt label)  ;; cxt: an association list. pairs of variables and values
     (let* ([lk (assoc label cxt)])
       (if lk (cdr lk) 'not-found)))
   (define (E ex env addr) ;;E is for evaluation, addr is the current address for MH
     (cond
      [(if? ex) (explode-if ex (lambda (l c t e) ;;explode-if is a helper function to easily access label, condition, then, else parts of the if-statement.
                                 (if (E c env addr) (E t env (cons l addr)) (E e env (cons l addr)))
                                 ))]
      [(lambda? ex)
       (explode-lambda ex (lambda (l vs c)
                            (let* ([closure `(closure (lambda ,l ,vs ,c) ,env)])
                              closure)))]
      [(factor? ex)
       (begin
         (explode-factor ex (lambda (lab formals call)
                              `(factor-closure (lambda ,lab ,(cons 'temp formals)
                                                  (call ,lab (ref ,lab *) (ref ,lab temp) ,call)
                                                  ) ,env))))]
      [(letrec? ex) (explode-letrec ex (lambda (l bs call)
                                         (let* ([local-binding-env
                                                 (fold (lambda (b e)
                                                         (extend e (car b) (E (cadr b) e addr)))
                                                       env bs)]
                                                [res (E call local-binding-env addr)])
                                           res)))]
      [(rv? ex) (rv->val ex)]
      [(call? ex) (explode-call ex (lambda (l f vs)
                                     (let* ([proc (E f env addr)]
                                            [vals (map (lambda (v)  (E v env addr))
                                                       vs)])

                                       (cond [(or (factor-closure? proc) ;;we would like to delay calls to the factors to the next stage
                                                  (closure? proc))
                                              (explode-closure proc (lambda (lam env2)
                                                                      (let* ([combined-env (append (if (list? (lambda->formals lam))
                                                                                                       (map cons (lambda->formals lam)
                                                                                                            (if (factor-closure? proc)
                                                                                                                (append
                                                                                                                 (cons 1.0 (cdr vals)))
                                                                                                                vals))
                                                                                                       (cons (lambda->formals lam) vals))
                                                                                                   env2 env)]
                                                                             [res (E (lambda->call lam) combined-env (cons l addr))])
                                                                        res)))]
                                             [(or (factor? proc) (lambda? proc)) (E `(call ,l ,proc ,@vals) env addr)]
                                             [(procedure? proc) (apply proc vals)]
                                             [else (pretty-print `(error-in-call-norm-eval ,proc))]))))]
      [(ref? ex) (let* ([lookup-res (lookup env (ref->var ex))])
                   (if (not-found? lookup-res)
                       (pretty-print `(not-found-norm-eval ,(ref->var ex)))
                       (cond [(rv? lookup-res)
                              (list-ref lookup-res 5)]
                             [else lookup-res])))]
      [(xrp? ex) (explode-xrp ex (lambda (lab name params)
                                   (let* ([curr-addr (cons lab addr)]
                                          [param-vals (map (lambda (p) (E p env addr)) params)]
                                          [res (apply (E (xrp->name ex) env curr-addr) param-vals)]) res)))]
      [(const? ex) (explode-const ex (lambda (lab c) c))]
      [else ex]))
   (E ex env addr))

 )
