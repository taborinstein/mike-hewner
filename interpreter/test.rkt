#lang racket

; To use these tests:
; Click "Run" in the upper right
; (r)

; If you find errors in your code, fix them, save your file, click the "Run" button again, and type (r)
; You can run a specific group of tests using (run-tests group-name)

(require "../testcode-base.rkt")
(require "interpreter.rkt")
(provide get-weights get-names individual-test test)

(define my-odd?
  (lambda (my-odd? my-even?)
    (lambda (num)
      (if (zero? num)
          #f
          (my-even? (sub1 num))))))
                      
(define my-even?
  (lambda (my-odd? my-even?)
    (lambda (num)
      (if (zero? num)
          #t
          (my-odd? (sub1 num))))))


(define sequal?-grading
  (lambda (l1 l2)
    (cond
     ((null? l1) (null? l2))
     ((null? l2) (null? l1))
     ((or (not (set?-grading l1))
          (not (set?-grading l2)))
      #f)
     ((member (car l1) l2) (sequal?-grading
                            (cdr l1)
                            (rember-grading
                             (car l1)
                             l2)))
     (else #f))))

(define rember-grading
  (lambda (a ls)
    (cond
     ((null? ls) ls)
     ((equal? a (car ls)) (cdr ls))
     (else (cons (car ls) (rember-grading a (cdr ls)))))))

(define test (make-test 
  (literals equal? ; (run-test literals)
    [(eval-one-exp ''()) '() 1] ; (run-test literals 1)
    [(eval-one-exp #t) #t 1] ; (run-test literals 2)
    [(eval-one-exp #f) #f 1] ; (run-test literals 3)
    [(eval-one-exp "") '"" 1] ; (run-test literals 4)
    [(eval-one-exp "test") '"test" 1] ; (run-test literals 5)
    [(eval-one-exp ''#(a b c)) #(a b c) 1] ; (run-test literals 6)
    [(eval-one-exp ''#5(a)) #5(a) 1] ; (run-test literals 7)
  )

  (quote equal? ; (run-test quote)
    [(eval-one-exp '(quote ())) '() 1] ; (run-test quote 1)
    [(eval-one-exp '(quote a)) 'a 1] ; (run-test quote 2)
    [(eval-one-exp '(quote (car (a b)))) '(car (a b)) 1] ; (run-test quote 3)
    [(eval-one-exp '(quote (lambda (x) (+ 1 x)))) '(lambda (x) (+ 1 x)) 1] ; (run-test quote 4)
  )

  (if equal? ; (run-test if)
    [(eval-one-exp '(if #t 5 6)) 5 1] ; (run-test if 1)
    [(eval-one-exp '(if 2 (if #f 3 4) 6)) 4 1] ; (run-test if 2)
    [(eval-one-exp '(if #f 5 6)) 6 1] ; (run-test if 3)
    [(eval-one-exp '(if 1 2 3)) 2 1] ; (run-test if 4)
    [(eval-one-exp '((lambda (x) (+ x 7)) (if #f 2 3))) 10 1] ; (run-test if 5)
  )

  (primitive-procedures equal? ; (run-test primitive-procedures)
    [(eval-one-exp '(+ (+ 1 2) 3 4)) 10 1] ; (run-test primitive-procedures 1)
    [(eval-one-exp '(- 10 1 (- 5 3))) 7 1] ; (run-test primitive-procedures 2)
    [(eval-one-exp '(* 2 (* 3 4) 2)) 48 1] ; (run-test primitive-procedures 3)
    [(eval-one-exp '(/ 6 2)) 3 1] ; (run-test primitive-procedures 4)
    [(eval-one-exp '(sub1 (add1 10))) 10 1] ; (run-test primitive-procedures 5)
    [(eval-one-exp '(not (zero? 3))) #t 1] ; (run-test primitive-procedures 6)
    [(eval-one-exp '(= 3 4)) #f 1] ; (run-test primitive-procedures 7)
    [(eval-one-exp '(>= 4 3)) #t 1] ; (run-test primitive-procedures 8)
    [(eval-one-exp '(cons 'a 'b)) '(a . b) 1] ; (run-test primitive-procedures 9)
    [(eval-one-exp '(car (cdr '(a b c)))) 'b 1] ; (run-test primitive-procedures 10)
    [(eval-one-exp '(list 'a 'b 'c)) '(a b c) 1] ; (run-test primitive-procedures 11)
    [(eval-one-exp '(null? '())) #t 1] ; (run-test primitive-procedures 12)
    [(eval-one-exp '(eq? 'a 'a)) #t 1] ; (run-test primitive-procedures 13)
    [(eval-one-exp '(equal? 'a 'a)) #t 1] ; (run-test primitive-procedures 14)
    [(eval-one-exp '(length '(a b c d e))) 5 1] ; (run-test primitive-procedures 15)
    [(eval-one-exp '(list->vector '(a b c))) #(a b c) 1] ; (run-test primitive-procedures 16)
    [(eval-one-exp '(list? 'a)) #f 1] ; (run-test primitive-procedures 17)
    [(eval-one-exp '(pair? '(a b))) #t 1] ; (run-test primitive-procedures 18)
    [(eval-one-exp '(vector->list '#(a b c))) '(a b c) 1] ; (run-test primitive-procedures 19)
    [(eval-one-exp '(vector? '#(a b c))) #t 1] ; (run-test primitive-procedures 20)
    [(eval-one-exp '(number? 5)) #t 1] ; (run-test primitive-procedures 21)
    [all-or-nothing 2 ; (run-test primitive-procedures 22)
      ((eval-one-exp '(symbol? 'a)) #t)
      ((eval-one-exp '(symbol? 5)) #f)]
    [(eval-one-exp '(caar '((a b) c))) 'a 1] ; (run-test primitive-procedures 23)
    [(eval-one-exp '(cadr '((a b) c))) 'c 1] ; (run-test primitive-procedures 24)
    [(eval-one-exp '(cadar '((a b) c))) 'b 1] ; (run-test primitive-procedures 25)
    [(eval-one-exp '(list (procedure? list) (procedure? (lambda (x y) (list (+ x y)))) (procedure? 'list))) '(#t #t #f) 3] ; (run-test primitive-procedures 26)
  )

  (lambda equal? ; (run-test lambda)
    [(eval-one-exp '((lambda (x) (+ 1 x)) 5)) 6 5] ; (run-test lambda 1)
    [(eval-one-exp '((lambda (x) (+ 1 x) (+ 2 (* 2 x))) 5)) 12 7] ; (run-test lambda 2)
    [(eval-one-exp '((lambda (a b)
               ((lambda (a b) 
                 ((lambda (f) 
                   (f (+ 3 a b)))
                  (lambda (a) (+ a b))))
                (+ a b) (- a b)))
             56 17)) 154 15] ; (run-test lambda 3)
    [(eval-one-exp '(((lambda (f) ((lambda (x) (f (lambda (y) ((x x) y)))) (lambda (x) (f (lambda (y) ((x x) y)))))) (lambda (g) (lambda (n) (if (zero? n) 1 (* n (g (- n 1))))))) 6)) 720 11] ; (run-test lambda 4)
    [(eval-one-exp '((lambda (Y H)
              ((Y H) (list list (lambda (x) x) 'list)))
             (lambda (f) ((lambda (x) (f (lambda (y) ((x x) y)))) (lambda (x) (f (lambda (y) ((x x) y)))) ))
             (lambda (g) (lambda (x) (if (null? x) '() (cons (procedure? (car x)) (g (cdr x))))))))
              '(#t #t #f) 11] ; (run-test lambda 5)
  )

  (begin equal? ; (run-test begin)
    [(eval-one-exp '(begin 1 2 3 4)) 4 3] ; (run-test begin 2)
    [(eval-one-exp '(begin (lambda (x) 3) (lambda (y) 4))) '<interpreter-procedure> 5] ; (run-test begin 2)
    [(eval-one-exp '(begin 1 (begin 2 (begin 3 4)))) 4 3] ; (run-test begin 3)
    [(eval-one-exp '((lambda (x) (begin (vector-set! x 1 42)(vector-set! x 1 17) (vector-set! x 1 88) (vector-ref x 1))) (vector 0 1 2 3))) 88 5] ; (run-test begin 4)
  )



             
  (primitive-procedures equal? ; (run-test primitive-procedures)
    [(eval-one-exp ' (list (procedure? +) (not (procedure? (+ 3 4))))) '(#t #t) 2] ; (run-test primitive-procedures 1)
    [(eval-one-exp ' (list (procedure? procedure?) (procedure? (lambda(x) x)) (not (procedure? '(lambda (x) x))))) '(#t #t #t) 2] ; (run-test primitive-procedures 2)
    [(eval-one-exp ' (list (procedure? list) (procedure? map) (procedure? apply) (procedure? #t))) '(#t #t #t #f) 2] ; (run-test primitive-procedures 3)
    [(eval-one-exp ' (map procedure? (list map car 3 (lambda(x) x) (lambda x x) ((lambda () 2))))) '(#t #t #f #t #t #f) 2] ; (run-test primitive-procedures 4)
    [(eval-one-exp '(apply list (list 3 4 5))) '(3 4 5) 2] ; (run-test primitive-procedures 5)
    [(eval-one-exp ' (list (vector? (vector 3)) (vector-ref (vector 2 4 5) (vector-ref (vector 2 4 5) 0)))) '(#t 5) 1] ; (run-test primitive-procedures 6)
    [(eval-one-exp '(length '(a b c d e))) 5 1] ; (run-test primitive-procedures 7)
    [(eval-one-exp '(vector->list '#(a b c))) '(a b c) 1] ; (run-test primitive-procedures 8)
    [(eval-one-exp ' (list (procedure? list) (procedure? (lambda (x y) (list (+ x y)))) (procedure? 'list))) '(#t #t #f) 3] ; (run-test primitive-procedures 9)
    [(eval-one-exp '(apply + '(1 2 3 4))) 10 2] ; (run-test primitive-procedures 10)
  )

;   (lambda-regression-tests equal? ; (run-test lambda-regression-tests)
;     [(eval-one-exp '((lambda (x) (+ 1 x)) 5)) 6 1] ; (run-test lambda-regression-tests 1)
;     [(eval-one-exp '((lambda (x) (+ 1 x) (+ 2 (* 2 x))) 5)) 12 1] ; (run-test lambda-regression-tests 2)
;     [(eval-one-exp ' ((lambda (a b) (let ((a (+ a b)) (b (- a b))) (let ((f (lambda (a) (+ a b)))) (f (+ 3 a b))))) 56 17)) 154 3] ; (run-test lambda-regression-tests 3)
;     [(eval-one-exp ' (((lambda (f) ((lambda (x) (f (lambda (y) ((x x) y)))) (lambda (x) (f (lambda (y) ((x x) y)))))) (lambda (g) (lambda (n) (if (zero? n) 1 (* n (g (- n 1))))))) 6)) 720 4] ; (run-test lambda-regression-tests 4)
;     [(eval-one-exp ' (let ((Y (lambda (f) ((lambda (x) (f (lambda (y) ((x x) y)))) (lambda (x) (f (lambda (y) ((x x) y))))))) (H (lambda (g) (lambda (x) (if (null? x) '() (cons (procedure? (car x)) (g (cdr x)))))))) ((Y H) (list list (lambda (x) x) 'list)))) '(#t #t #f) 4] ; (run-test lambda-regression-tests 5)
;   )

;   (lambda-with-variable-args equal? ; (run-test lambda-with-variable-args)
;     [(eval-one-exp '((lambda x (car x) (cdr x)) 'a 'b 'c)) '(b c) 5] ; (run-test lambda-with-variable-args 1)
;   )

;   (let equal? ; (run-test literals)
;     [(eval-one-exp '(let () 3)) 3 1] ; (run-test literals 1)
;     [(eval-one-exp '(let () 3 4 5)) 5 1] ; (run-test literals 2)
;     [(eval-one-exp '(let ([x 3]) 5 x)) 3 1] ; (run-test literals 3)
;     [(eval-one-exp '(let ([x 3][y 4]) (list x y))) '(3 4) 1] ; (run-test literals 4)
;     [(eval-one-exp '(let ([x 3][y (let ([z 42]) (+ (- z 1) 1))]) (list x y))) '(3 42) 2] ; (run-test literals 5)
;     [(eval-one-exp '(let ([x 3][y 42]) (let ([z y]) (+ z 1)) (let ([z x]) (+ z 1) z))) 3 2] ; (run-test literals 6)
;     [(eval-one-exp '(let ([x 3][y 42]) (let ([z y]) (let ([z x]) (list z x y))))) '(3 3 42) 2] ; (run-test literals 7)
;   )

;    (let* equal? ; (run-test literals)
;     [(eval-one-exp '(let* () 3)) 3 1] ; (run-test literals 1)
;     [(eval-one-exp '(let* () 3 4 5)) 5 1] ; (run-test literals 2)
;     [(eval-one-exp '(let* ([x 3]) 5 x)) 3 1] ; (run-test literals 3)
;     [(eval-one-exp '(let* ([x 3][y (+ x 1)]) (list x y))) '(3 4) 2] ; (run-test literals 4)
;     [(eval-one-exp '(let* ([x 3][y (let ([z (+ x 1)]) z)]) (list x y))) '(3 4) 2] ; (run-test literals 5)
;     [(eval-one-exp '(let* ([x 3][y (+ x 1)]) (let* ([z (+ y 1)][a (+ z 1)]) (let* ([b (+ a 1)]) (list x y z a b))))) '(3 4 5 6 7) 3] ; (run-test literals 6)
;   )

;    (and equal? ; (run-test literals)
;     [(eval-one-exp '(and 3)) 3 1] ; (run-test literals 1)
;     [(eval-one-exp '(and)) #t 1] ; (run-test literals 1)
;     [(eval-one-exp '(and 3 4 5)) 5 2] ; (run-test literals 2)
;     [(eval-one-exp '(and 3 #f 5)) #f 2] ; (run-test literals 3)
;     [(eval-one-exp '(and 3 4 #f)) #f 2] ; (run-test literals 4)
;     [(eval-one-exp '((lambda (v) (and 3 ((lambda () (vector-set! v 1 42) #f)) 5)) (vector 3 4 5))) #f 3] ; (run-test literals 5)
;     [(eval-one-exp '(
;             (lambda (v) 
;                 (and 3 
;                 ((lambda () (vector-set! v 1 42) #f)) 
;                     ((lambda ()(vector-set! v 1 88)))
;                         ) v) (vector 3 4 5))) '#(3 42 5) 3] ; (run-test literals 6)
;   )

;    (or equal? ; (run-test literals)
;     [(eval-one-exp '(or)) #f 1] ; (run-test literals 1)
;     [(eval-one-exp '(or 3)) 3 1] ; (run-test literals 1)
;     [(eval-one-exp '(or 3 4 5)) 3 2] ; (run-test literals 2)
;     [(eval-one-exp '(or 3 #f 5)) 3 2] ; (run-test literals 3)
;     [(eval-one-exp '(or #f 4 5)) 4 2] ; (run-test literals 4)
;     [(eval-one-exp '((lambda (v) (or ((lambda () (vector-set! v 1 42) #f)) 5)) (vector 3 4 5))) 5 3] ; (run-test literals 5)
;     [(eval-one-exp '((lambda (v) (or 3 ((lambda () (vector-set! v 1 42) #f))) v) (vector 3 4 5))) '#(3 4 5) 3] ; (run-test literals 6)
;   )

;    (begin equal? ; (run-test literals)
;     [(eval-one-exp '(begin)) (void) 1] ; (run-test literals 1)
;     [(eval-one-exp '(begin 3)) 3 1] ; (run-test literals 1)
;     [(eval-one-exp '(begin 3 4 5)) 5 1] ; (run-test literals 2)
;     [(eval-one-exp  '(begin 3 (begin 4 5) 6)) 6 2] ; (run-test literals 3)
;     [(eval-one-exp '(begin 3 (begin 4 (begin 5 (begin 6))))) 6 2] ; (run-test literals 4)
;     [(eval-one-exp '((lambda (v) (begin (vector-set! v 0 (+ (vector-ref v 0) 1)) (vector-set! v 0 (+ (vector-ref v 0) 1)) v)) (vector 5))) '#(7) 3] ; (run-test literals 5)
;   )

;   (cond equal? ; (run-test literals)
;     [(eval-one-exp '(cond)) (void) 2] ; (run-test literals 1)
;     [(eval-one-exp '(cond [3 4])) 4 2] ; (run-test literals 2)
;     [(eval-one-exp '(cond [3 4 5])) 5 2] ; (run-test literals 3)
;     [(eval-one-exp '((lambda (x) (cond [(= x 3) (+ x 3)][(= x 7) (+ x 7)][else (+ x 9)][(= x 10)(+ x 10)])) 3)) 6 3]
;     [(eval-one-exp '((lambda (x) (cond [(= x 3) (+ x 3)][(= x 7) (+ x 7)][else (+ x 9)][(= x 10)(+ x 10)])) 7)) 14 3]
;     [(eval-one-exp '((lambda (x) (cond [(= x 3) (+ x 3)][(= x 7) (+ x 7)][else (+ x 9)][(= x 10)(+ x 10)])) 42)) 51 3]
;     [(eval-one-exp '((lambda (x) (cond [(= x 3) (+ x 3)][(= x 7) (+ x 7)][else (+ x 9)][(= x 10)(+ x 10)])) 10)) 19 3]
;     )
  
;   (one-armed-if equal? ; (run-test one-armed-if)
;     [(eval-one-exp '(let ((x (vector 7))) (if (< 4 5) (vector-set! x 0 (+ 3 (vector-ref x 0)))) (if (< 4 2) (vector-set! x 0 (+ 6 (vector-ref x 0)))) (vector-ref x 0))) 10 5] ; (run-test one-armed-if 1)
;   )

;   (quasiquote equal?
;               [(begin (quasiquote-enabled?)
;                       (eval-one-exp '`,(+ 1 2))) 3 .1]
;               [(eval-one-exp '(let ((var 'val))
;                                 `(foo ,(cons 2 '()) () (,var var)))) '(foo (2) () (val var)) .1]
;               [(eval-one-exp '`(1 ,@(list 2 3) 4)) '(1 2 3 4) .1]
;               [(eval-one-exp '(let ((var (list 1 2)))
;                                 `(,@var a ,var b ,@var (c ,@var)))) '(1 2 a (1 2) b 1 2 (c 1 2)) .1]
;               [(eval-one-exp '(let ((stx '(let ((x 1) (y 2)) x y (+ x y))))
;                                 `((lambda ,(map car (cadr stx)) ,@(cddr stx)) ,@(map cadr (cadr stx)))))
;                '((lambda (x y) x y (+ x y)) 1 2) .1]
              
;               )

;   (add-macro-interpreter equal?
;                          [(begin
;                             (add-macro-interpreter 'varpair '(lambda (stx) `(list (quote ,(cadr stx)) ,(cadr stx))))
;                             (eval-one-exp '(let ((x 3))
;                                              (varpair x)))) '(x 3) .1]
;                          [(begin
;                             (add-macro-interpreter 'let2
;                                                    '(lambda (stx) `((lambda ,(map car (cadr stx)) ,@(cddr stx)) ,@(map cadr (cadr stx)))))
;                             (eval-one-exp '(let2 ((x 1) (y 2)) (+ x y)))) 3 .1]
;                          [(eval-one-exp '(begin
;                                            (define-syntax varpair2 (lambda (stx) `(list (quote ,(cadr stx)) ,(cadr stx))))
;                                            (let ((y 3))
;                                              (varpair2 y)))) '(y 3) .1]
;                          [(eval-one-exp '(begin
;                                            (define-syntax varpair3 (lambda (stx) `(list (quote ,(cadr stx)) ,(cadr stx))))
;                                            (define-syntax let3 (lambda (stx) `((lambda ,(map car (cadr stx)) ,@(cddr stx)) ,@(map cadr (cadr stx)))))
;                                            (let3 ((y 4))
;                                              (varpair3 y)))) '(y 4) .2]
;                          )




;   (basics equal? ; (run-test basics)
;     [(eval-one-exp ' (letrec ((fact (lambda (x) (if (zero? x) 1 (* x (fact (- x 1))))))) (map fact '(0 1 2 3 4 5)))) '(1 1 2 6 24 120) 6] ; (run-test basics 1)
;     [(eval-one-exp ' (let f ((n 8) (acc 1)) (if (= n 0) acc (f (sub1 n) (* acc n))))) 40320 6] ; (run-test basics 2)
;     [(eval-one-exp ' (let ((n 5)) (let f ((n n) (acc 1)) (if (= n 0) acc (f (sub1 n) (* acc n)))))) 120 6] ; (run-test basics 3)
;     [(eval-one-exp ' (letrec ((even? (lambda (n) (if (zero? n) #t (odd? (- n 1))))) (odd? (lambda (m) (if (zero? m) #f (even? (- m 1)))))) (list (odd? 3) (even? 3) (odd? 4) (even? 4)))) '(#t #f #f #t) 6] ; (run-test basics 4)
;   )

;   (answers-are-sets sequal?-grading ; (run-test answers-are-sets)
;     [(eval-one-exp ' (letrec ((union (lambda (s1 s2) (cond ((null? s1) s2) ((member? (car s1) s2) (union (cdr s1) s2)) (else (cons (car s1) (union (cdr s1) s2)))))) (member? (lambda (sym ls) (cond ((null? ls) #f) ((eqv? (car ls) sym) #t) (else (member? sym (cdr ls))))))) (union '(a c e d k) '(e b a d c)))) '(k e b d a c) 8] ; (run-test answers-are-sets 1)
;     [(eval-one-exp ' (letrec ((product (lambda (x y) (if (null? y) '() (let loop ((x x) (accum '())) (if (null? x) accum (loop (cdr x) (append (map (lambda (s) (list (car x) s)) y) accum)))))))) (product '(1 2 3) '(a b)))) '((3 a) (2 b) (3 b) (2 a) (1 a) (1 b)) 8] ; (run-test answers-are-sets 2)
;   )

;   (additional equal? ; (run-test additional)
;     [(eval-one-exp ' (letrec ((sort (lambda (pred? l) (if (null? l) l (dosort pred? l (length l))))) (merge (lambda (pred? l1 l2) (cond ((null? l1) l2) ((null? l2) l1) ((pred? (car l2) (car l1)) (cons (car l2) (merge pred? l1 (cdr l2)))) (else (cons (car l1) (merge pred? (cdr l1) l2)))))) (dosort (lambda (pred? ls n) (if (= n 1) (list (car ls)) (let ((mid (quotient n 2))) (merge pred? (dosort pred? ls mid) (dosort pred? (list-tail ls mid) (- n mid)))))))) (sort > '(3 8 1 4 2 5 6)))) '(8 6 5 4 3 2 1) 10] ; (run-test additional 1)
;   )

;   (subst-leftmost equal? ; (run-test subst-leftmost)
;     [(eval-one-exp ' (letrec ( (apply-continuation (lambda (k val) (k val))) (subst-left-cps (lambda (new old slist changed unchanged) (let loop ((slist slist) (changed changed) (unchanged unchanged)) (cond ((null? slist) (apply-continuation unchanged #f)) ((symbol? (car slist)) (if (eq? (car slist) old) (apply-continuation changed (cons new (cdr slist))) (loop (cdr slist) (lambda (changed-cdr) (apply-continuation changed (cons (car slist) changed-cdr))) unchanged))) (else (loop (car slist) (lambda (changed-car) (apply-continuation changed (cons changed-car (cdr slist)))) (lambda (t) (loop (cdr slist) (lambda (changed-cdr) (apply-continuation changed (cons (car slist) changed-cdr))) unchanged))))))))) (let ((s '((a b (c () (d e (f g)) h)) i))) (subst-left-cps 'new 'e s (lambda (changed-s) (subst-left-cps 'new 'q s (lambda (wont-be-changed) 'whocares) (lambda (r) (list changed-s)))) (lambda (p) "It's an error to get here"))))) '(((a b (c () (d new (f g)) h)) i)) 10] ; (run-test subst-leftmost 1)
;   )

;   (y2 equal?
;       [(let ([o? (y2 my-odd? my-odd? my-even?)]
;              [e? (y2 my-even? my-odd? my-even?)])
;          (list (o? 0) (o? 1) (o? 5) (o? 6) (e? 0) (e? 1) (e? 5) (e? 6))) '(#f #t #t #f #t #f #f #t) 0.5])
;   (advanced-letrec equal?
;                    [(advanced-letrec
;                      ((o? (lambda (num)
;                             (if (zero? num)
;                                 #f
;                                 (e? (sub1 num)))))
;                       (e? (lambda (num)
;                             (if (zero? num)
;                                 #t
;                                 (o? (sub1 num))))))
;                      (list (o? 0) (o? 1) (o? 5) (o? 6) (e? 0) (e? 1) (e? 5) (e? 6))) '(#f #t #t #f #t #f #f #t) 0.25]
;                    [(advanced-letrec
;                      ([a (lambda (lst) (if (null? lst) '() (cons (+ 1 (car lst)) (b (cdr lst)))))]
;                       [b (lambda (lst) (if (null? lst) '() (cons (+ 2 (car lst)) (c (cdr lst)))))]
;                       [c (lambda (lst) (if (null? lst) '() (cons (+ 3 (car lst)) (d (cdr lst)))))]
;                       [d (lambda (lst) (if (null? lst) '() (cons (+ 4 (car lst)) (a (cdr lst)))))])
;                      (a '(0 0 0 0 0 0 0 0 0))) '(1 2 3 4 1 2 3 4 1) 0.25]
;                    )



;   (set!-local-variables equal? ; (run-test set!-local-variables)
;     [(eval-one-exp '(let ((f #f) (x 3)) (set! f (lambda (n) (+ 3 (* n 10)))) (set! x 7) (f x))) 73 5] ; (run-test set!-local-variables 1)
;     [(eval-one-exp '((lambda (x) (set! x (+ x 1)) (+ x 2)) 90)) 93 5] ; (run-test set!-local-variables 2)
;     [(eval-one-exp '(let ((x 5) (y 3)) (let ((z (begin (set! x (+ x y)) x))) (+ z (+ x y))))) 19 5] ; (run-test set!-local-variables 3)
;     [(eval-one-exp '(let ((a 5)) (if (not (= a 6)) (begin (set! a (+ 1 a)) (set! a (+ 1 a))) 3) (+ 1 a))) 8 6] ; (run-test set!-local-variables 4)
;     [(eval-one-exp '(let ((f #f)) (let ((dummy (begin (set! f (lambda (n) (+ 3 (* n 10)))) 3))) (f 4)))) 43 6] ; (run-test set!-local-variables 5)
;   )

;   (simple-defines equal? ; (run-test simple-defines)
;     [(eval-one-exp '(begin (define a 5) (+ a 3))) 8 5] ; (run-test simple-defines 1)
;     [(eval-one-exp '(begin (define c 5) (define d (+ c 2)) (+ d (add1 c)))) 13 6] ; (run-test simple-defines 2)
;     [(eval-one-exp '(begin (define e 5) (let ((f (+ e 2))) (set! e (+ e f)) (set! f (* 2 f)) (list e f)))) '(12 14) 6] ; (run-test simple-defines 3)
;     [(eval-one-exp '(begin (define ff (letrec ((ff (lambda (x) (if (= x 1) 2 (+ (* 2 x) (ff (- x 2))))))) ff)) (ff 7))) 32 6] ; (run-test simple-defines 4)
;     [(begin (eval-one-exp '(define cons +)) (eval-one-exp '(cons 2 3))) 5 4] ; (run-test simple-defines 5)
;     [(eval-one-exp '(begin (define double-fact (lambda (x) (fact (* 2 x)))) (define fact (lambda (x) (if (zero? x) 1 (* x (fact (sub1 x)))))) (double-fact 4))) 40320 12] ; (run-test simple-defines 6)
;   )

;   (letrec-and-define equal? ; (run-test letrec-and-define)
;     [(begin (reset-global-env) (eval-one-exp '(letrec ((f (lambda (n) (if (= n 0) 0 (+ n (f (sub1 n))))))) (f 10)))) 55 6] ; (run-test letrec-and-define 1)
;     [(eval-one-exp '(letrec ((f (lambda (n) (if (zero? n) 0 (+ 4 (g (sub1 n)))))) (g (lambda (n) (if (zero? n) 0 (+ 3 (f (sub1 n))))))) (f (g (f 5))))) 221 6] ; (run-test letrec-and-define 2)
;     [(begin (reset-global-env) (eval-one-exp '(define zer0? (lambda (x) (= x 0)))) (eval-one-exp '(letrec ([f (lambda (n) (if (zer0? n) 0 (+ n (f (sub1 n)))))]) (f 10)))) 55 7] ; (run-test letrec-and-define 3)
;   )

;   (named-let-and-define equal? ; (run-test named-let-and-define)
;     [(eval-one-exp '(begin (define fact (lambda (n) (let loop ((n n) (m 1)) (if (= n 0) m (loop (- n 1) (* m n)))))) (fact 5))) 120 8] ; (run-test named-let-and-define 1)
;     [(eval-one-exp '(let fact ((n 5) (m 1)) (if (= n 0) m (fact (- n 1) (* m n))))) 120 8] ; (run-test named-let-and-define 2)
;     [(begin (reset-global-env) (eval-one-exp '(define rotate-linear (letrec ((reverse (lambda (lyst revlist) (if (null? lyst) revlist (reverse (cdr lyst) (cons (car lyst) revlist)))))) (lambda (los) (let loop ((los los) (sofar '())) (cond ((null? los) los) ((null? (cdr los)) (cons (car los) (reverse sofar '()))) (else (loop (cdr los) (cons (car los) sofar))))))))) (eval-one-exp '(rotate-linear '(1 2 3 4 5 6 7 8)))) '(8 1 2 3 4 5 6 7) 9] ; (run-test named-let-and-define 3)
;     [(begin (reset-global-env) (eval-one-exp '(define fib-memo (let ((max 2) (sofar '((1 . 1) (0 . 1)))) (lambda (n) (if (< n max) (cdr (assq n sofar)) (let* ((v1 (fib-memo (- n 1))) (v2 (fib-memo (- n 2))) (v3 (+ v2 v1))) (set! max (+ n 1)) (set! sofar (cons (cons n v3) sofar)) v3)))))) (eval-one-exp '(fib-memo 15))) 987 9] ; (run-test named-let-and-define 4)
;     [(begin (reset-global-env) (eval-one-exp '(define f1 (lambda (x) (f2 (+ x 1))))) (eval-one-exp '(define f2 (lambda (x) (* x x)))) (eval-one-exp '(f1 3))) 16 7] ; (run-test named-let-and-define 5)
;     [(begin (reset-global-env) (eval-one-exp '(define ns-list-recur (lambda (seed item-proc list-proc) (letrec ((helper (lambda (ls) (if (null? ls) seed (let ((c (car ls))) 
;         (if 
;             (or 
;                 (pair? c) 
;                 (null? c)
;             ) (list-proc (helper c) (helper (cdr ls))) (item-proc c (helper (cdr ls))))))))) helper)))) (eval-one-exp '(define append (lambda (s t) (if (null? s) t (cons (car s) (append (cdr s) t)))))) (eval-one-exp '(define reverse* (let ((snoc (lambda (x y) (append y (list x))))) (ns-list-recur '() snoc snoc)))) (eval-one-exp '(reverse* '(1 (2 3) (((4))) () 5)))) '(5 () (((4))) (3 2) 1) 10] ; (run-test named-let-and-define 6)
;   )

;   (set!-global-variables equal? ; (run-test set!-global-variables)
;     [(begin (reset-global-env) (eval-one-exp '(define a 3)) (eval-one-exp '(set! a 7)) (eval-one-exp 'a)) 7 7] ; (run-test set!-global-variables 1)
;     [(begin (reset-global-env) (eval-one-exp '(define a 3)) (eval-one-exp '(define f '())) (eval-one-exp '(set! f (lambda (x) (+ x 1)))) (eval-one-exp '(f a))) 4 7] ; (run-test set!-global-variables 2)
;     [(begin (reset-global-env) (eval-one-exp '(define a 5)) (eval-one-exp '(define f '())) (eval-one-exp '(set! f (lambda (x) (if (= x 0) 1 (* x (f (- x 1))))))) (eval-one-exp '(f a))) 120 7] ; (run-test set!-global-variables 3)
;     [(begin (reset-global-env) (eval-one-exp '(define a 5)) (eval-one-exp '(let ((b 7)) (set! a 9))) (eval-one-exp 'a)) 9 7] ; (run-test set!-global-variables 4)
;   )

;   (order-matters! equal? ; (run-test order-matters!)
;     [(eval-one-exp '(let ((r 2) (ls '(3)) (count 7)) (let loop () (if (> count 0) (begin (set! ls (cons r ls)) (set! r (+ r count)) (set! count (- count 1)) (loop)))) (list r ls count))) '(30 (29 27 24 20 15 9 2 3) 0) 12] ; (run-test order-matters! 1)
;     [(eval-one-exp 
;     '(begin 
;         (define latest 1) 
;         (define total 1) 
;         (or 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1))
;                 (set! total (+ total latest))
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             ) 
;             (begin 
;                 (set! latest (+ latest 1)) 
;                 (set! total (+ total latest)) 
;               ; (display "latest ") (displayln latest) (display "total ") (displayln total) (display "( > total 50) ") (displayln (> total 50))
;                 (> total 50)
;             )
;         ) total)) 55 12] ; (run-test order-matters! 2)
;   )

;   (misc equal? ; (run-test misc)
;     [(eval-one-exp '(apply apply (list + '(1 2)))) 3 5] ; (run-test misc 1)
;     [(eval-one-exp '(apply map (list (lambda (x) (+ x 3)) '(2 4)))) '(5 7) 5] ; (run-test misc 2)
;     [(begin (reset-global-env) (eval-one-exp '(let ([x 2]) (or (begin (set! x (add1 x)) #f) (begin (set! x (add1 x)) #f) (begin (set! x (+ 10 x)) #t)) (or x (set! x 25) x)))) 14 8] ; (run-test misc 3)
;   )


;   (legacy equal? ; (run-test legacy)
;     [(eval-one-exp '(let ((x 5) (y 3)) (let ((z (begin (set! x (+ x y)) x))) (+ z (+ x y))))) 19 0.1] ; (run-test legacy 1)
;     [(begin (reset-global-env) (eval-one-exp '(begin (define cde 5) (define def (+ cde 2)) (+ def (add1 cde))))) 13 0.1] ; (run-test legacy 2)
;     [(begin (reset-global-env) (eval-one-exp '(letrec ((f (lambda (n) (if (zero? n) 0 (+ 4 (g (sub1 n)))))) (g (lambda (n) (if (zero? n) 0 (+ 3 (f (sub1 n))))))) (g (f (g (f 5))))))) 773 0.1] ; (run-test legacy 3)
;     [(begin (reset-global-env) (eval-one-exp '(define rotate-linear (letrec ((reverse (lambda (lyst revlist) (if (null? lyst) revlist (reverse (cdr lyst) (cons (car lyst) revlist)))))) (lambda (los) (let loop ((los los) (sofar '())) (cond ((null? los) los) ((null? (cdr los)) (cons (car los) (reverse sofar '()))) (else (loop (cdr los) (cons (car los) sofar))))))))) (eval-one-exp '(rotate-linear '(1 2 3 4 5 6 7 8)))) '(8 1 2 3 4 5 6 7) 0.1] ; (run-test legacy 4)
;     [(begin (reset-global-env) (eval-one-exp '(let ((r 2) (ls '(3)) (count 7)) (let loop () (if (> count 0) (begin (set! ls (cons r ls)) (set! r (+ r count)) (set! count (- count 1)) (loop)))) (list r ls count)))) '(30 (29 27 24 20 15 9 2 3) 0) 0.1] ; (run-test legacy 5)
;     [(eval-one-exp '(apply apply (list + '(1 2)))) 3 0.1] ; (run-test legacy 6)
;     [(eval-one-exp '(apply map (list (lambda (x) (+ x 3)) '(2 4)))) '(5 7) 0.1] ; (run-test legacy 7)
;     [(eval-one-exp '(letrec ( (apply-continuation (lambda (k val) (k val))) (subst-left-cps (lambda (new old slist changed unchanged) (let loop ((slist slist) (changed changed) (unchanged unchanged)) (cond ((null? slist) (apply-continuation unchanged #f)) ((symbol? (car slist)) (if (eq? (car slist) old) (apply-continuation changed (cons new (cdr slist))) (loop (cdr slist) (lambda (changed-cdr) (apply-continuation changed (cons (car slist) changed-cdr))) unchanged))) (else (loop (car slist) (lambda (changed-car) (apply-continuation changed (cons changed-car (cdr slist)))) (lambda (t) (loop (cdr slist) (lambda (changed-cdr) (apply-continuation changed (cons (car slist) changed-cdr))) unchanged))))))))) (let ((s '((a b (c () (d e (f g)) h)) i))) (subst-left-cps 'new 'e s (lambda (changed-s) (subst-left-cps 'new 'q s (lambda (wont-be-changed) 'whocares) (lambda (r) (list changed-s)))) (lambda (p) "It's an error to get here"))))) '(((a b (c () (d new (f g)) h)) i)) 0.2] ; (run-test legacy 8)
;     [(eval-one-exp '((lambda () 3 4 5))) 5 0.1] ; (run-test legacy 9)
;   )

;   (simple-call/cc equal? ; (run-test simple-call/cc)
;     [(eval-one-exp '(+ 5 (call/cc (lambda (k) (+ 6 (k 7)))))) 12 2] ; (run-test simple-call/cc 1)
;     [(eval-one-exp '(+ 3 (call/cc (lambda (k) (* 2 5))))) 13 2] ; (run-test simple-call/cc 2)
;     [(eval-one-exp '(+ 5 (call/cc (lambda (k) (or #f #f (+ 7 (k 4)) #f))))) 9 2] ; (run-test simple-call/cc 3)
;     [(eval-one-exp '(list (call/cc procedure?))) '(#t) 2] ; (run-test simple-call/cc 4)
;     [(eval-one-exp '(+ 2 (call/cc (lambda (k) (+ 3 (let* ((x 5) (y (k 7))) (+ 10 (k 5)))))))) 9 2] ; (run-test simple-call/cc 5)
;     [(eval-one-exp '((car (call/cc list)) (list cdr 1 2 3))) '(1 2 3) 2] ; (run-test simple-call/cc 6)
;     [(eval-one-exp '(let ((a 5) (b 6)) (set! a (+ 7 (call/cc (lambda (k) (set! b (k 11)))))) (list a b))) '(18 6) 2] ; (run-test simple-call/cc 7)
;   )

;   (complex-call/cc equal? ; (run-test complex-call/cc)
;     [(begin (reset-global-env) (eval-one-exp '(define xxx #f)) (eval-one-exp '(+ 5 (call/cc (lambda (k) (set! xxx k) 2)))) (eval-one-exp '(* 7 (xxx 4)))) 9 2] ; (run-test complex-call/cc 1)
;     [(begin (eval-one-exp '(define break-out-of-map #f)) (eval-one-exp '(set! break-out-of-map (call/cc (lambda (k) (lambda (x) (if (= x 7) (k 1000) (+ x 4))))))) (eval-one-exp '(map break-out-of-map '(1 3 5 7 9 11))) (eval-one-exp 'break-out-of-map)) 1000 2] ; (run-test complex-call/cc 2)
;     [(begin (eval-one-exp '(define jump-into-map #f)) (eval-one-exp '(define do-the-map (lambda (x) (map (lambda (v) (if (= v 7) (call/cc (lambda (k) (set! jump-into-map k) 100)) (+ 3 v))) x)))) (eval-one-exp '(do-the-map '(3 4 5 6 7 8 9 10)))) '(6 7 8 9 100 11 12 13) 2] ; (run-test complex-call/cc 3)
;     [(begin (eval-one-exp '(define jump-into-map #f)) (eval-one-exp '(define do-the-map (lambda (x) (map (lambda (v) (if (= v 7) (call/cc (lambda (k) (set! jump-into-map k) 100)) (+ 3 v))) x)))) (eval-one-exp '(list (do-the-map '(3 4 5 6 7 8 9 10)))) (eval-one-exp '(jump-into-map 987654321))) '((6 7 8 9 987654321 11 12 13)) 2] ; (run-test complex-call/cc 4)
;     [(eval-one-exp '(let ((y (call/cc (call/cc (call/cc call/cc))))) (y list) (y 4))) '(4) 2] ; (run-test complex-call/cc 5)
;     [(eval-one-exp '(+ 4 (apply call/cc (list (lambda (k) (* 2 (k 5))))))) 9 2] ; (run-test complex-call/cc 6)
;     [(eval-one-exp '(letrec ((a (lambda (x) (+ 12 (call/cc (lambda (k) (if (k x) 7 (a (- x 3))))))))) (+ 6 (a 7)))) 25 2] ; (run-test complex-call/cc 7)
;     [(eval-one-exp '(map (call/cc (lambda (k) (lambda (v) (if (= v 1) (k add1) (+ 4 v))))) '( 2 1 4 1 4))) '(3 2 5 2 5) 2] ; (run-test complex-call/cc 8)
;     [(eval-one-exp '(begin (define a 4) (define f (lambda () (call/cc (lambda (k) (set! a (+ 1 a)) (set! a (+ 2 a)) (k a) (set! a (+ 5 a)) a)))) (f))) 7 2] ; (run-test complex-call/cc 9)
;   )

;   (exit-list equal? ; (run-test exit-list)
;     [(eval-one-exp '(+ 4 (exit-list 5 (exit-list 6 7)))) '(6 7) 2] ; (run-test exit-list 1)
;     [(eval-one-exp '(+ 3 (- 2 (exit-list 5)))) '(5) 2] ; (run-test exit-list 2)
;     [(eval-one-exp '(- 7 (if (exit-list 3) 4 5))) '(3) 2] ; (run-test exit-list 3)
;     [(eval-one-exp '(call/cc (lambda (k) (+ 100 (exit-list (+ 3 (k 12))))))) 12 2] ; (run-test exit-list 4)
;     [(eval-one-exp '(call/cc (lambda (k) (+ 100 (k (+ 3 (exit-list 12))))))) '(12) 2] ; (run-test exit-list 5)
;   )


  ))

(define set?-grading
  (lambda (s)
    (cond [(null? s) #t]
          [(not (list? s)) #f]
          [(member (car s) (cdr s)) #f]
          [else (set?-grading (cdr s))])))
  (implicit-run test)