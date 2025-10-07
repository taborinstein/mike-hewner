#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define-datatype expression expression?  
  [var-exp        ; variable references
   (id symbol?)]
  [lit-exp        ; "Normal" data.  Did I leave out any types?
   (datum
    (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))]
  [lambda-exp
   (params list?)
   (body expression?)]
  [let-exp
   (param list?)
   (body expression?)]
  [letrec-exp
   (param list?)
   (body expression?)]
  [let*-exp
   (param list?)
   (body expression?)]
  [set!-exp
   (id symbol?)
   (body expression?)]
  [if-exp
   (test expression?)
   (then expression?)
   (else expression?)]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of? expression?))]  
  )
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])

  
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
          (cond [(null? mlst) #t]
                [(or (not (list? (car mlst))) (not (symbol? (caar mlst))) (not (= 2 (length (car mlst))))) #f]
                [else (cpl-recur (cdr mlst))]
                )))))

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (lit-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(string? datum) (lit-exp datum)]
      [(boolean? datum) (lit-exp datum)]
      [(vector? datum) (lit-exp datum)]
      [(pair? datum) (cond [(eqv? (1st datum) 'lambda) (cond [(> 3 (length datum)) (error 'parse-exp "bad abstraction size: ~s" datum)]
                                                             [(and (list? (2nd datum)) (not (null? (filter (lambda (a) (not (symbol? a))) (2nd datum))))) (error 'parse-exp "bad abstraction parameter: ~s" datum)]
                                                             [else (lambda-exp (lit-exp (2nd datum))
                                                                               (if (list? (3rd datum))
                                                                                          (parse-exp (3rd datum))
                                                                                          (lit-exp (cddr datum))))]
                                                             )]
                           [(eqv? (1st datum) 'if) (cond [(not (= 4 (length datum))) (error 'parse-exp "bad if-statement size: ~s" datum)]
                                                         [else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))]
                                                         )]
                           [(or (eqv? (1st datum) 'let)
                                (eqv? (1st datum) 'letrec)
                                (eqv? (1st datum) 'let*)) (cond [(> 3 (length datum)) (error 'parse-exp "bad let size: ~s" datum)]
                                                                [(and (not (null? (2nd datum))) (not (check-param-list (2nd datum)))) (error 'parse-exp "invalid let params: ~s" datum)]
                                                                [else (cond [(eqv? (1st datum) 'let) (let-exp (parse-exp (2nd datum)) (if (list? (3rd datum))
                                                                                                                                                 (parse-exp (3rd datum))
                                                                                                                                                 (lit-exp (cddr datum))))]
                                                                            [(eqv? (1st datum) 'letrec) (letrec-exp (parse-exp (2nd datum)) (if (list? (3rd datum))
                                                                                                                                                       (parse-exp (3rd datum))
                                                                                                                                                       (lit-exp (cddr datum))))]
                                                                            [(eqv? (1st datum) 'let*) (let*-exp (parse-exp (2nd datum)) (if (list? (3rd datum))
                                                                                                                                                   (parse-exp (3rd datum))
                                                                                                                                                   (lit-exp (cddr datum))))]
                                                                            )])]
                           [(eqv? (1st datum) 'set!) (cond [(not (= 3 (length datum))) (error 'parse-exp "bad set! size: ~s" datum)]
                                                           [(not (symbol? (2nd datum))) (error 'parse-exp "invalid variable: ~s" datum)]
                                                           [else (set!-exp (2nd datum) (parse-exp (3rd datum)))])]
                           [else (cond [(not (list? datum)) (error 'parse-exp "bad application format: ~s" datum)]
                                       [else (app-exp (map parse-exp datum))]
                                       )]
                           )]
      [(null? datum) (lit-exp '(()))]
      [else (error 'parse-exp "bad expression: ~s" datum)]
      )))


;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

; Pick your favorite representation based on the lecture

(define apply-env
  (lambda (env id)
    (if (equal? id '+)
        (prim-proc '+)
        (error "this is not a real environment implementation"))))

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
    (eval-exp form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env init-env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp rator)]
                     [args (eval-rands rands)])
                 (apply-proc proc-value args))]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands)
    (map eval-exp rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))



(define init-env         ; you'll want to have a global environment with the prim procs and maybe other stuff
  '())



(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (+ (first args) (second args))]
      [(-) (- (first args) (second args))]
      [(*) (* (first args) (second args))]
      [(add1) (+ (first args) 1)]
      [(sub1) (- (first args) 1)]
      [(cons) (cons (first args) (second args))]
      [(=) (= (first args) (second args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))