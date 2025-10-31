'(app-exp 
    (lambda-exp 
        (lit-exp (a)) 
            ((if-exp 
                (app-exp (var-exp a) ()) 
                (var-exp a) 
                (lit-exp #f))))
          ((lit-exp 1)))


'(define-exp
  ns-list-recur
  (lambda-exp
   (lit-exp (seed item-proc list-proc))
   ((letrec-exp
     (helper)
     ((ls))
     (((if-exp
        (app-exp (var-exp null?) ((var-exp ls)))
        (var-exp seed)
        (app-exp
         (lambda-exp
          (lit-exp (c))
          ((if-exp (app-exp (lambda-exp (lit-exp (__then))
                                        ((if-exp (app-exp (var-exp __then) ())
                                                 (var-exp __then)
                                                 (app-exp (var-exp null?) ((var-exp c))))))
                            ((app-exp (var-exp pair?) ((var-exp c)))))
                   (app-exp (var-exp list-proc)
                            ((app-exp (var-exp helper) ((var-exp c)))
                             (app-exp (var-exp helper) ((app-exp (var-exp cdr) ((var-exp ls)))))))
                   (app-exp (var-exp item-proc)
                            ((var-exp c) (app-exp (var-exp helper)
                                                  ((app-exp (var-exp cdr) ((var-exp ls))))))))))
         ((app-exp (var-exp car) ((var-exp ls))))))))
     ((var-exp helper))))))
