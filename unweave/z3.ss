#!r6rs

;; Communicating with Z3 (todo: FFI?)
;; return value: an environment of assignments or #f (unsat)
;; Creating temporary files

(library

 (unweave z3)

 (export run-z3)

 (import (rnrs)
         (only (scheme-tools) system format)
         (only (ikarus) fork waitpid read-line with-input-from-string))

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

 )