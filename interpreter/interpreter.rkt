#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)
(require racket/trace)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this
; code with your expression datatype from A11b

(define-datatype expression
                 expression?
                 [var-exp ; variable references
                  (id symbol?)]
                 [lit-exp ; "Normal" data.  Did I leave out any types?
                  (datum (lambda (x)
                           (ormap (lambda (pred) (pred x))
                                  (list number? vector? boolean? symbol? string? pair? null?))))]
                 [lambda-exp (params list?) (body expression?)]
                 [quote-exp (quot list?)]
                 [let-exp (param list?) (init-exp (listof expression?)) (body expression?)]
                 [letrec-exp (param list?) (init-exp (listof expression?)) (body expression?)]
                 [let*-exp (param list?) (init-exp (listof expression?)) (body expression?)]
                 [set!-exp (id symbol?) (body expression?)]
                 [if-exp (test expression?) (then expression?) (else expression?)]
                 [app-exp ; applications
                  (rator expression?)
                  (rands (list-of? expression?))])

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val? [prim-proc (name symbol?)])

;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Again, you'll probably want to use your code from A11b

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

; Check to see if lst is a list of pairs with symbols in their car
(define check-param-list
  (lambda (lst)
    (if (or (not (list? lst)) (null? lst))
        #f
        (let cpl-recur ([mlst lst])
          (cond
            [(null? mlst) #t]
            [(or (not (list? (car mlst))) (not (symbol? (caar mlst))) (not (= 2 (length (car mlst)))))
             #f]
            [else (cpl-recur (cdr mlst))])))))

(define parse-exp
  (lambda (datum)
    (cond
      ; (if (equal? datum 'quote) (lit-exp ''quote)
      [(symbol? datum) (lit-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(string? datum) (lit-exp datum)]
      [(boolean? datum) (lit-exp datum)]
      [(vector? datum) (lit-exp datum)]
      [(pair? datum)
       (cond
         [(eqv? (1st datum) 'quote)
          (cond
            [(not (= 2 (length datum))) (error 'parse-exp "bad abstraction size: ~s" datum)]
            [else (quote-exp (list (quote quote) datum))])]
         [(eqv? (1st datum) 'lambda)
          (cond
            [(> 3 (length datum)) (error 'parse-exp "bad abstraction size: ~s" datum)]
            [(and (list? (2nd datum))
                  (not (null? (filter (lambda (a) (not (symbol? a))) (2nd datum)))))
             (error 'parse-exp "bad abstraction parameter: ~s" datum)]
            [else
             (lambda-exp (lit-exp (2nd datum))
                         (if (list? (3rd datum))
                             (parse-exp (3rd datum))
                             (lit-exp (cddr datum))))])]
         [(eqv? (1st datum) 'if)
          (cond
            [(not (= 4 (length datum))) (error 'parse-exp "bad if-statement size: ~s" datum)]
            [else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))])]
         [(or (eqv? (1st datum) 'let) (eqv? (1st datum) 'letrec) (eqv? (1st datum) 'let*))
          (cond
            [(> 3 (length datum)) (error 'parse-exp "bad let size: ~s" datum)]
            [(and (not (null? (2nd datum))) (not (check-param-list (2nd datum))))
             (error 'parse-exp "invalid let params: ~s" datum)]
            [else
             (cond
               [(eqv? (1st datum) 'let)
                (let-exp (parse-exp (2nd datum))
                         (if (list? (3rd datum))
                             (parse-exp (3rd datum))
                             (lit-exp (cddr datum))))]
               [(eqv? (1st datum) 'letrec)
                (letrec-exp (parse-exp (2nd datum))
                            (if (list? (3rd datum))
                                (parse-exp (3rd datum))
                                (lit-exp (cddr datum))))]
               [(eqv? (1st datum) 'let*)
                (let*-exp (parse-exp (2nd datum))
                          (if (list? (3rd datum))
                              (parse-exp (3rd datum))
                              (lit-exp (cddr datum))))])])]
         [(eqv? (1st datum) 'set!)
          (cond
            [(not (= 3 (length datum))) (error 'parse-exp "bad set! size: ~s" datum)]
            [(not (symbol? (2nd datum))) (error 'parse-exp "invalid variable: ~s" datum)]
            [else (set!-exp (2nd datum) (parse-exp (3rd datum)))])]
         [else
          (cond
            [(not (list? datum)) (error 'parse-exp "bad application format: ~s" datum)]
            [else (app-exp (parse-exp (1st datum)) (map parse-exp (cdr datum)))])])]
      [(null? datum) (lit-exp '(()))]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

;; environment type definitions

(define scheme-value? (lambda (x) #t))

(define-datatype
 environment
 environment?
 [empty-env-record]
 [extended-env-record (syms (list-of? symbol?)) (vals (list-of? scheme-value?)) (env environment?)])

(define empty-env (lambda () (empty-env-record)))

(define extend-env (lambda (syms vals env) (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los]
               [pos 0])
      (cond
        [(null? los) #f]
        [(eq? sym (car los)) pos]
        [else (loop (cdr los) (add1 pos))]))))

(define *prim-proc-names*
  '(+ -
      *
      /
      add1
      sub1
      zero?
      not
      =
      <
      <=
      >
      >=
      cons
      car
      cdr
      list
      null?
      assq
      eq?
      equal?
      length
      list->vector
      list?
      pair?
      procedure?
      vector->list
      vector
      make-vector
      vector-ref
      vector?
      number?
      symbol?
      vector-set!
      display
      newline))
(define init-env ; for now, our initial global environment only contains
  (extend-env ; procedure names.  Recall that an environment associates
   *prim-proc-names* ;  a value (not an expression) with an identifier.
   (map prim-proc *prim-proc-names*)
   (empty-env)))

(define global-env init-env)
(define apply-global-env
  (lambda (sym)
    (cases environment
           global-env
           [empty-env-record () (error 'global-env "PANIC: This should never occur!")]
           [extended-env-recor
            (syms vals env)
            (let ([pos (list-find-position sym syms)])
              (if (number? pos)
                  (list-ref vals pos)
                  (error 'global-env "variable ~s not bound in global env" sym)))])))

(define apply-env
  (lambda (env sym)
    (cases environment
           env
           [empty-env-record () (apply-global-env sym)]
           [extended-env-record
            (syms vals env)
            (let ([pos (list-find-position sym syms)])
              (if (number? pos)
                  (list-ref vals pos)
                  (apply-env env sym)))])))
;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.

;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp (empty-env) form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp) ; IC-ADDED - environment parameter
    (cases
     expression
     exp
     [lit-exp (datum) datum]
     [quote-exp (datum) (cadr (cadr datum))]
     [lambda-exp (a b) 'nyi]
     [letrec-exp (a b c) 'nyi]
     [let*-exp (a b c) 'nyi]
     [set!-exp (a b) 'nyi]
     [if-exp (a b c) 'nyi]
     [var-exp (id) (apply-env env id)]
     [app-exp
      (rator rands)
      (let ([proc-value (eval-exp env rator)] ; IC-ADDED - passed environment through
            [args (eval-rands env rands)]) ; IC-ADDED - passed environment through
        (apply-proc proc-value args))]
     [let-exp
      (vars init-exps bodies) ; IC-ADDED - added basic let interpretation
      (let* ([eval-init-exps
              (eval-rands
               env
               init-exps)] ; IC-ADDED - evaluate initialization expression with parent environment
             [let-env (extend-env
                       vars
                       eval-init-exps
                       env)]) ; IC-ADDED -  create let environment with new initialization expressions
        (eval-exp let-env
                  (car bodies)))] ; IC-ADDED - evaluate the body of the let with new environment
     [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))
; evaluate the list of operands, putting results into a list

(define eval-rands (lambda (env rands) (map (λ (x) (eval-exp env x)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val
           proc-value
           [prim-proc (op) (apply-prim-proc op args)]
           ; You will add other cases
           [else (error 'apply-proc "Attempt to apply bad procedure: ~s" proc-value)])))

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (+ (1st args) (2nd args))]
      [(-) (- (1st args) (2nd args))]
      [(*) (* (1st args) (2nd args))]
      [(/) (/ (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(null?) (null? (car args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(list?) (list? (car args))]
      [(pair?) (pair? (car args))]
      [(vector?) (vector? (car args))]
      [(number?) (number? (car args))]
      [(symbol?) (symbol? (car args))]
      [(procedure?) (procedure? (car args))]
      [(not) (not (car args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(car) (caar (args))]
      [(cdr) (cdar (args))]
      [(list) args]
      [(length) (length (car args))]
      [(assq) (assq (car args))]
      [(list->vector) (list->vector (car args))]
      [(vector->list) (vector->list (car args))]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector) (vector (1st args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display (car args))]
      [(newline) (newline)]
      [else (error 'apply-prim-proc "Bad primitive procedure name: ~s" prim-proc)])))
(define rep ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer)
      (newline)
      (rep)))) ; tail-recursive, so stack doesn't grow.

(define eval-one-exp (lambda (x) (top-level-eval (parse-exp x))))
; (eval-exp '(empty-env-record) '(app-exp (lit-exp quoquotete) ((lit-exp (())))))
(displayln (parse-exp '(+ (+ 1 2) 3 4)))
; (eval-one-exp ''())
;
; (eval-exp (empty-env) '(app-exp))
; (trace eval-exp)
