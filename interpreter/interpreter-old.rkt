#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)
(provide reset-global-env)
(require racket/trace)
(provide add-macro-interpreter)
(define add-macro-interpreter (lambda x (error "nyi")))
(provide quasiquote-enabled?)
(define quasiquote-enabled?
  (lambda () (error "nyi"))) ; make this return 'yes if you're trying quasiquote
(provide y2
         advanced-letrec)
(define y2 (lambda (which f1 f2) (error "nyi")))
(define-syntax (advanced-letrec stx)
  (syntax-case stx ()
    [(advanced-letrec ((fun-name fun-body) ...) letrec-body) #'(error "nyi")]))

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this
; code with your expression datatype from A11b

(define-datatype
 expression
 expression?
 [var-exp (id symbol?)]
 [lit-exp
  (datum (lambda (x)
           (ormap (lambda (pred) (pred x))
                  (list number? vector? boolean? symbol? string? pair? null?))))]
 [lambda-exp (params list?) (bodies (listof expression?))]
 [lambda-2-exp (params expression?) (bodies (listof expression?))]
 [quote-exp (quot list?)]
 [let-exp (param list?) (init-exp (listof expression?)) (bodies (listof expression?))]
 [letrec-exp
  (procnames (listof symbol?))
  (idss (listof (listof symbol?)))
  (bodiess (listof (listof expression?)))
  (letrec-bodies (listof expression?))]
 [let*-exp (param list?) (init-exp (listof expression?)) (bodies (listof expression?))]
 [set!-exp (id symbol?) (body expression?)]
 [define-exp (id symbol?) (body expression?)]
 [if-exp (test expression?) (then expression?) (else expression?)]
 [if-2-exp (test expression?) (then expression?)]
 [begin-exp (bodies (listof expression?))]
 [app-exp (rator expression?) (rands (list-of? expression?))]
 [and-exp (rands (listof expression?))]
 [or-exp (rands (listof expression?))]
 [cond-exp
  (tests (lambda (x) (ormap (lambda (pred) (pred x)) (list (listof expression?) void?))))
  (thens (lambda (x) (ormap (lambda (pred) (pred x)) (list (listof expression?) void?))))]
 [void-exp (const void?)])

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val
                 proc-val?
                 [prim-proc (name symbol?)] ; Primitive procedures
                 [closure-proc
                  (params (listof symbol?))
                  (body (listof expression?))
                  (env environment?)] ; Standard lambda procedures
                 [closure-proc-2
                  (param symbol?)
                  (body (listof expression?))
                  (env environment?)]) ; Arbitrary variable lambda procedure

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
; Used as a helper method for determining 'let' expressions.
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
      [(symbol? datum) (var-exp datum)]
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
         [(eqv? (1st datum) 'begin)
          (begin-exp (map (λ (d)
                            (cond
                              [(list? d) (parse-exp d)]
                              [(symbol? d) (var-exp d)]
                              [else (lit-exp d)]))
                          (cdr datum)))]
         [(eqv? (1st datum) 'lambda)
          (cond
            [(> 3 (length datum)) (error 'parse-exp "bad abstraction size: ~s" datum)]
            [(and (list? (2nd datum))
                  (not (null? (filter (lambda (a) (not (symbol? a))) (2nd datum)))))
             (error 'parse-exp "bad abstraction parameter: ~s" datum)]
            [else
             ((if (list? (2nd datum)) lambda-exp lambda-2-exp) (lit-exp (2nd datum))
                                                               (map (λ (d)
                                                                      ; (if (list? d)
                                                                      (parse-exp d)
                                                                      ; (lit-exp d))
                                                                      )
                                                                    (cddr datum)))])]
         [(eqv? (1st datum) 'if)
          (cond
            [(not (or (= 4 (length datum)) (= 3 (length datum))))
             (error 'parse-exp "bad if-statement size: ~s" datum)]
            [(= 3 (length datum)) (if-2-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
            [else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))])]
         [(or (eqv? (1st datum) 'let) (eqv? (1st datum) 'letrec) (eqv? (1st datum) 'let*))
          (cond
            [(> 3 (length datum)) (error 'parse-exp "bad let size: ~s" datum)]
            [(and (not (symbol? (2nd datum)))
                  (not (null? (2nd datum)))
                  (not (check-param-list (2nd datum))))
             (error 'parse-exp "invalid let params: ~s" datum)]
            [else
             (cond
               [(eqv? (1st datum) 'let)
                (if (symbol? (2nd datum))
                    (letrec-exp (list (2nd datum))
                                (list (map car (3rd datum)))
                                (map (lambda (x) (list (parse-exp x))) (cdddr datum))
                                (list (app-exp (var-exp (2nd datum))
                                               (map (lambda (x) (parse-exp (cadr x))) (3rd datum)))))
                    (let-exp (map lit-exp (map car (2nd datum)))
                             (map parse-exp (map cadr (2nd datum)))
                             (map parse-exp (cddr datum))))]
               [(eqv? (1st datum) 'let*)
                (let*-exp (map lit-exp (map car (2nd datum)))
                          (map parse-exp (map cadr (2nd datum)))
                          (map parse-exp (cddr datum)))]
               [(eqv? (1st datum) 'letrec)
                (letrec-exp (map car (2nd datum))
                            (map (lambda (x) (cadr (cadr x))) (2nd datum))
                            (map (lambda (x) (list (parse-exp (caddr (cadr x))))) (2nd datum))
                            (map parse-exp (cddr datum)))])])]
         [(eqv? (1st datum) 'set!)
          (cond
            [(not (= 3 (length datum))) (error 'parse-exp "bad set! size: ~s" datum)]
            [(not (symbol? (2nd datum))) (error 'parse-exp "invalid variable: ~s" datum)]
            [else (set!-exp (2nd datum) (parse-exp (3rd datum)))])]
         [(eqv? (1st datum) 'define)
          (cond
            [(not (= 3 (length datum))) (error 'parse-exp "bad define size: ~s" datum)]
            [(not (symbol? (2nd datum))) (error 'parse-exp "invalid variable: ~s" datum)]
            [else (define-exp (2nd datum) (parse-exp (3rd datum)))])]
         [(eqv? (1st datum) 'and) (and-exp (map parse-exp (cdr datum)))]
         [(eqv? (1st datum) 'or) (or-exp (map parse-exp (cdr datum)))]
         [(eqv? (1st datum) 'cond)
          (if (= 1 (length datum))
              (cond-exp (void) (void))
              (cond-exp (map (lambda (x) (parse-exp (car x))) (cdr datum))
                        (map (lambda (x) (parse-exp (append (list 'begin) (cdr x)))) (cdr datum))))]
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
 [extended-env-record (syms (list-of? symbol?)) (vals (list-of? scheme-value?)) (env environment?)]
 [recur-extended-env-record
  (procnames (list-of? symbol?))
  (idss (list-of? (list-of? symbol?)))
  (bodiess (list-of? (list-of? expression?)))
  (old-env environment?)])

(define empty-env (lambda () (empty-env-record)))

(define extend-env (lambda (syms vals env) (extended-env-record syms (map box vals) env)))

(define extend-recur-env
  (lambda (procnames idss bodiess old-env)
    (recur-extended-env-record procnames idss bodiess old-env)))

; IC SUGGESTION - Create new procedure specifcally for letrec
; 1 - Create an environment take takes a vector
; 2 - Create the letrec closures
; 3 - Use a for-loop that edits the environment vector (I believe syms and vals)

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
      quotient
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
      cadr
      caar
      cadr
      cdar
      cddr
      caaar
      caadr
      cadar
      caddr
      cdaar
      cdadr
      cddar
      cdddr
      caaaar
      caaadr
      caadar
      caaddr
      cadaar
      cadadr
      caddar
      cadddr
      cdaaar
      cdaadr
      cdadar
      cdaddr
      cddaar
      cddadr
      cdddar
      cddddr
      displayln
      list
      list-tail
      null?
      assq
      eq?
      eqv?
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
      newline
      map
      apply
      append
      and
      or))
(define init-env ; for now, our initial global environment only contains
  (extend-env ; procedure names.  Recall that an environment associates
   *prim-proc-names* ;  a value (not an expression) with an identifier.
   (map prim-proc *prim-proc-names*)
   (empty-env)))

(define global-env init-env)

(define apply-global-env
  (lambda (sym)
    #;(cases
       environment
       global-env
       [empty-env-record () (error 'global-env "PANIC: This should never occur!")]
       [extended-env-record
        (syms vals env)
        (let ([pos (list-find-position sym syms)])
          (if (number? pos)
              (begin
                ; (display "list-ref ")
                ; (displayln (list-ref vals pos))
                (list-ref vals pos))
              (error 'global-env "variable ~s not bound in global env" sym)))]
       [recur-extended-env-record
        (procnames idss bodiess letrec-bodies)
        (error
         'global-env
         "Achievement unlocked: How did we get here?")]) ; Don't get rid of this section, just in case
    (deref (apply-global-env-ref sym))))

(define apply-env
  (lambda (env sym)
    #;(cases environment
             env
             [empty-env-record () (apply-global-env sym)]
             [extended-env-record
              (syms vals env)
              (let ([pos (list-find-position sym syms)])
                (if (number? pos)
                    (list-ref vals pos)
                    (apply-env env sym)))]
             [recur-extended-env-record
              (procnames idss bodiess old-env)
              (let ([pos (list-find-position sym procnames)])
                (if (number? pos)
                    (closure-proc (list-ref idss pos) (list-ref bodiess pos) env)
                    (apply-env old-env sym)))]) ; Don't get rid of this section, just in case
    (deref (apply-env-ref env sym))))

; (trace extended-env-record)

; Returns a reference to the variable in question
(define apply-global-env-ref
  (lambda (sym)
    (cases environment
           global-env
           [empty-env-record () (error 'global-env "PANIC: This should never occur!")]
           [extended-env-record
            (syms vals env)
            (let ([pos (list-find-position sym syms)])
              (if (number? pos)
                  (list-ref vals pos)
                  (error 'global-env "variable ~s not bound in global env" sym)))]
           [recur-extended-env-record
            (procnames idss bodiess letrec-bodies)
            (error 'global-env "Achievement unlocked: How did we get here?")])))

(define apply-env-ref
  (lambda (env sym)
    (cases environment
           env
           [empty-env-record () (apply-global-env-ref sym)]
           [extended-env-record
            (syms vals env)
            (let ([pos (list-find-position sym syms)])
              (if (number? pos)
                  (list-ref vals pos)
                  (apply-env-ref env sym)))]
           [recur-extended-env-record
            (procnames idss bodiess old-env)
            (let ([pos (list-find-position sym procnames)])
              (if (number? pos)
                  (box (closure-proc (list-ref idss pos) (list-ref bodiess pos) env))
                  (apply-env-ref old-env sym)))])))

; Gets the value stored in the location that is reference by ref
(define deref (lambda (ref) (unbox ref)))

; Sets the value stored in ref to val
(define set-ref! (lambda (ref val) (set-box! ref val)))

; Resets the global environemtn
(define reset-global-env (lambda () (set! global-env init-env)))

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
  (lambda (exp)
    (cases expression
           exp
           [var-exp (datum) exp]
           [lit-exp (datum) exp]
           [lambda-exp (params bodies) (lambda-exp params (map syntax-expand bodies))] ; DONE
           [lambda-2-exp (params bodies) (lambda-2-exp params (map syntax-expand bodies))] ; DONE
           [quote-exp (quot) exp] ; DONE
           [if-exp
            (test then else)
            (if-exp (syntax-expand test) (syntax-expand then) (syntax-expand else))] ; DONE
           [if-2-exp (test then) (if-2-exp (syntax-expand test) (syntax-expand then))] ; DONE
           [let-exp
            (params init-exp bodies)
            (app-exp (lambda-exp (lit-exp (map cadr params)) (map syntax-expand bodies))
                     (map syntax-expand init-exp))] ; DONE
           [letrec-exp
            (procnames idss bodiess letrec-bodies)
            (letrec-exp procnames
                        idss
                        (map (lambda (x) (list (syntax-expand (car x)))) bodiess)
                        (map syntax-expand letrec-bodies))] ; DONE
           [let*-exp
            (params init-exps bodies)
            (let let*-recur ([plst params]
                             [ilst init-exps])
              (if (null? plst)
                  (app-exp (lambda-exp (lit-exp '()) bodies) (list (lit-exp 0)))
                  (app-exp (lambda-exp (lit-exp (list (cadar plst)))
                                       (list (let*-recur (cdr plst) (cdr ilst))))
                           (list (syntax-expand (car ilst))))))] ; DONE
           [set!-exp (id body) (set!-exp id (syntax-expand body))] ; DONE
           [define-exp (id body) (define-exp id (syntax-expand body))] ; DONE
           [begin-exp (bodies) (begin-exp (map syntax-expand bodies))] ; DONE
           [app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))] ; DONE
           [and-exp
            (rands)
            (cond
              [(null? rands) (lit-exp #t)]
              [(null? (cdr rands)) (syntax-expand (car rands))]
              [else
               (if-exp (syntax-expand (car rands))
                       (syntax-expand (and-exp (cdr rands)))
                       (lit-exp #f))])] ; DONE
           [or-exp
            (rands)
            (cond
              [(null? rands) (lit-exp #f)]
              [(null? (cdr rands)) (syntax-expand (car rands))]
              [else
               (app-exp (lambda-exp (lit-exp (list '__then))
                                    (list (if-exp (var-exp '__then)
                                                  (var-exp '__then)
                                                  (syntax-expand (or-exp (cdr rands))))))
                        (list (syntax-expand (car rands))))])]
           ;   (if-exp (syntax-expand (car rands))
           ;           (syntax-expand (car rands))
           ;           (syntax-expand (or-exp (cdr rands))))])] ; DONE
           [cond-exp
            (tests thens)
            (cond
              [(or (void? tests) (null? tests)) (void-exp (void))]
              [(eqv? (cadar tests) 'else) (syntax-expand (car thens))]
              [else
               (if-exp (syntax-expand (car tests))
                       (syntax-expand (car thens))
                       (syntax-expand (cond-exp (cdr tests) (cdr thens))))])] ; DONE
           [void-exp (const) exp])))

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
(define do-define
  (lambda (id ex)
    (set! global-env (extend-env (list id) (list (eval-exp global-env ex)) global-env))))
(define check-proc-val (lambda (v) (if (proc-val? v) '<interpreter-procedure> v)))
(define top-level-eval
  (lambda (form)
    (cases expression
           form
           [define-exp (id ex) (do-define id ex)]
           [begin-exp
            (bodies)
            (if (null? bodies)
                (void)
                (check-proc-val (car (reverse (map (λ (x)
                                                     (if (equal? (car x) 'define-exp)
                                                         (do-define (cadr x) (caddr x))
                                                         (eval-exp global-env x)))
                                                   bodies)))))]
           [else (let ([result (eval-exp global-env form)]) (check-proc-val result))])))
; (trace top-level-eval)
; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp)
    ; (display "\x1b[31m")
    ; (display exp)
    ; (displayln "\x1b[0m")
    (cases
     expression
     exp
     [lit-exp (datum) datum]
     [quote-exp (datum) (cadr (cadr datum))]
     [lambda-exp (args bodies) (closure-proc (eval-exp env args) bodies env)]
     [lambda-2-exp (args bodies) (closure-proc-2 (eval-exp env args) bodies env)]
     [begin-exp
      (bodies)
      (let ([evals (map (λ (p) (eval-exp env p)) bodies)])
        (if (null? evals)
            (void)
            (car (reverse evals))))]
     [letrec-exp
      (procnames idss bodiess letrec-bodies)
      (eval-exp (extend-recur-env procnames idss bodiess env) (begin-exp letrec-bodies))]
     [set!-exp (id body) (set-ref! (apply-env-ref env id) (eval-exp env body))]
     [define-exp (id body) 'nyi]
     [if-exp
      (if-cond if-then if-else)
      (if (eval-exp env if-cond)
          (eval-exp env if-then)
          (eval-exp env if-else))]
     [if-2-exp
      (test then)
      (if (eval-exp env test)
          (eval-exp env then)
          (void))]
     [var-exp (id) (apply-env env id)]
     [app-exp
      (rator rands)
      (let ([proc-value (eval-exp env rator)] ; IC-ADDED - passed environment through
            [args (eval-rands env rands)]) ; IC-ADDED - passed environment through
         (display "\x1b[32m")
    (display "EVAL-RANDS")
    (display " ")
    (display args)
    (displayln "\x1b[0m")
        (apply-proc env proc-value args))] ; args ; (map (lambda (x) (if (proc-val? x) (cases proc-val x [prim-proc (op) op] [closure-proc (params bodies env) 'nyi]) x)) args)
     [let-exp
      (vars init-exps bodies) ; IC-ADDED - added basic let interpretation
      (let* ([eval-init-exps
              (eval-rands
               env
               init-exps)] ; IC-ADDED - evaluate initialization expression with parent environment
             [let-env (extend-env
                       (map (λ (x) (eval-exp env x)) vars)
                       eval-init-exps
                       env)]) ; IC-ADDED -  create let environment with new initialization expressions
        (car (reverse (map (λ (x) (eval-exp let-env x))
                           bodies))))] ; IC-ADDED - evaluate the body of the let with new environment
     [let*-exp
      (vars init-exps bodies)
      (eval-exp env
                (if (null? vars)
                    (let-exp vars init-exps bodies)
                    (let-exp (list (car vars))
                             (list (car init-exps))
                             (list (let*-exp (cdr vars) (cdr init-exps) bodies)))))]
     [and-exp (rands) (apply-proc env (prim-proc 'and) (eval-rands env rands))] ; temporary
     [or-exp (rands) (apply-proc env (prim-proc 'or) (eval-rands env rands))] ; temporary
     [cond-exp
      (tests thens)
      (if (void? tests)
          (void)
          (eval-exp env (car thens)))]
     [void-exp (const) (void)]
     [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))
; evaluate the list of operands, putting results into a list

(define eval-rands (lambda (env rands) (map (λ (x) (eval-exp env x)) rands)))
; (trace apply-env)
;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (env proc-value args)
    (cases proc-val
           proc-value
           [prim-proc (op) (apply-prim-proc env op args)]
           [closure-proc
            (params bodies env)
            (let ([closure-env (extend-env params args env)])
              (car (reverse (map (λ (body) (eval-exp closure-env body)) bodies))))]
           [closure-proc-2
            (param bodies env)
            (let ([closure-env (extend-env (list param) (list args) env)])
              (car (reverse (map (λ (body) (eval-exp closure-env body)) bodies))))]
           ; You will add other cases
           [else (error 'apply-proc "Attempt to apply bad procedure: ~s" proc-value)])))

(define apply-prim-proc
  (lambda (env prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(quotient) (quotient (1st args) (2nd args))]
      [(=) (apply = args)]
      [(>) (apply > args)]
      [(>=) (apply >= args)]
      [(<) (apply < args)]
      [(<=) (apply <= args)]
      [(zero?) (zero? (car args))]
      [(null?) (null? (car args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(list?) (list? (car args))]
      [(pair?) (pair? (car args))]
      [(vector?) (vector? (car args))]
      [(number?) (number? (car args))]
      [(symbol?) (symbol? (car args))]
      [(procedure?)
       (if (proc-val? (car args))
           #t
           #f)] ; (procedure? (car args)) ; (if (proc-val? (car args)) #t #f)
      [(not) (not (car args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(car) (caar args)]
      [(caar) (caar (car args))]
      [(cadr) (cadr (car args))]
      [(cdar) (cdar (car args))]
      [(cddr) (cddr (car args))]
      [(caaar) (caaar (car args))]
      [(caadr) (caadr (car args))]
      [(cadar) (cadar (car args))]
      [(caddr) (caddr (car args))]
      [(cdaar) (cdaar (car args))]
      [(cdadr) (cdadr (car args))]
      [(cddar) (cddar (car args))]
      [(cdddr) (cdddr (car args))]
      [(caaaar) (caaaar (car args))]
      [(caaadr) (caaadr (car args))]
      [(caadar) (caadar (car args))]
      [(caaddr) (caaddr (car args))]
      [(cadaar) (cadaar (car args))]
      [(cadadr) (cadadr (car args))]
      [(caddar) (caddar (car args))]
      [(cadddr) (cadddr (car args))]
      [(cdaaar) (cdaaar (car args))]
      [(cdaadr) (cdaadr (car args))]
      [(cdadar) (cdadar (car args))]
      [(cdaddr) (cdaddr (car args))]
      [(cddaar) (cddaar (car args))]
      [(cddadr) (cddadr (car args))]
      [(cdddar) (cdddar (car args))]
      [(cddddr) (cddddr (car args))]
      [(displayln) (displayln (car args))]
      [(cdr) (cdar args)]
      [(cdr) (cadar args)]
      [(list) args]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [(length) (length (car args))]
      [(assq) (assq (car args) (cadr args))]
      [(list->vector) (list->vector (car args))]
      [(vector->list) (vector->list (car args))]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector) (apply vector args)]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display (car args))]
      [(newline) (newline)]
      [(map)
       (let tail ([proc (1st args)]
                  [lst (cadr args)])
         (if (null? lst)
             '()
             (append (list (apply-proc env proc (list (car lst)))) (tail proc (cdr lst)))))]
      [(apply) (apply-proc env (1st args) (2nd args))]
      [(append) (apply append args)]
      [(and)
       (let and-recur ([lst args]
                       [cur #t])
         (displayln args)
         (cond
           [(null? lst) cur]
           [(null? (cdr lst)) (and cur (car lst))]
           [(not (car lst)) #f]
           [(not (cadr lst)) #f]
           [(and (not (eqv? #f (car lst))) (not (eqv? #f (cadr lst))))
            (and-recur (cdr lst) (cadr lst))]
           [else #f]))]
      [(or)
       (let or-recur ([lst args]
                      [cur #f])
         (cond
           [(null? lst) cur]
           [(not (car lst)) (or-recur (cdr lst) #f)]
           [else (car lst)]))]
      [else (error 'apply-prim-proc "Bad primitive procedure name: ~s" prim-proc)])))

(define rep ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer)
      (newline)
      (rep)))) ; tail-recursive, so stack doesn't grow.

(define eval-one-exp (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))
