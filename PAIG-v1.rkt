#lang typed/racket

;; Project fully implemented, all tests passed

(require typed/rackunit)

;; Assignment 3
;; PAIG3 must include following functions:
;; parse(Sexp) -> ExprC
;; parse-fundef(Sexp) -> FundefC
;; parse-prog(Sexp) -> (listof FundefC)
;; interp-fns(listof FundefC) -> Real
;; interp(ExprC (listof FundefC)) -> Real
;; top-interp(Sexp) -> Real

;; -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
;; Type-defs

;; ExprC struct definitions
(define-type ExprC (U NumC binopC idC appC ifleq0?))
(struct NumC ([n : Real]) #:transparent)
(struct binopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : idC] [arg : ExprC]) #:transparent)
(struct ifleq0? ([check1 : ExprC] [result1 : ExprC] [else : ExprC]) #:transparent)

;; Function definition struct
(define-type DefnC (U FunC))
(struct FunC ([name : idC] [params : idC] [body : ExprC]) #:transparent)

;; -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
;; Interpreters and helper functions

;; Purpose: Interprets an expression written in PAIG to find its value, and uses the list of
;; functions to interpret any applications into their value (a real number)
(define (interp [exp : ExprC] [funs : (Listof FunC)]) : Real
  (match exp
    [(NumC n) n]
    [(binopC s l r) (eval s l r funs)]
    [(ifleq0? c r e)
     (if (<= (interp c funs) 0)
         (interp r funs)
         (interp e funs))]
    [(appC f val)
     (interp (subst (NumC (interp val funs)) (find-param f funs) (find-expr f funs)) funs)]))

;; Purpose: A helper function for interpreting binops which will take in a symbol, two arguments,
;; and a list of functions, and then evaluate those arguments based on the operation symbol given to
;; return a real value
(define (eval [op : Symbol] [arg1 : ExprC] [arg2 : ExprC] [funs : (Listof FunC)]) : Real
  (match op
    ['+ (+ (interp arg1 funs) (interp arg2 funs))]
    ['- (- (interp arg1 funs) (interp arg2 funs))]
    ['* (* (interp arg1 funs) (interp arg2 funs))]
    ['/
     (match (interp arg2 funs)
       [0 (error 'eval "(PAIG) cannot divide by zero")]
       [other (/ (interp arg1 funs) other)])]))

;; Purpose: A helper function used that takes in a variable, a value, and an expression,
;; and returns the given expression with the given variable replaced by the given value
(define (subst [val : ExprC] [var : Symbol] [in : ExprC]) : ExprC
  (match in
    [(NumC n) in]
    [(idC s) (cond
               [(symbol=? s var) val]
               [else (error 'subst "(PAIG) Unbound identifier: ~e" s)])]
    [(appC f e) (appC f (subst val var e))]
    [(binopC s l r) (binopC s (subst val var l) (subst val var r))]
    [(ifleq0? c r e) (ifleq0? (subst val var c) (subst val var r) (subst val var e))]))

;; Purpose: A helper function that searches the list of functions for the matching name, and
;; returns the name of the function if it exists
(define (find-func [f-name : idC] [funs : (Listof FunC)]) : idC
  (cond
    [(empty? funs) (error 'find-func (format "(PAIG) Function {~a} not defined" (idC-s f-name)))]
    [else
     (match (first funs)
       [(FunC n p b)
        (cond
          [(symbol=? (idC-s f-name) (idC-s n)) n]
          [else (find-func f-name (rest funs))])])]))

;; Purpose: A helper function that searches the list of functions for the matching name, and
;; returns the parameter symbol of the found function
(define (find-param [f-name : idC] [funs : (Listof FunC)]) : Symbol
  (cond
    [(empty? funs) (error 'find-param (format "(PAIG) Function {~a} not defined or invalid parameter" (idC-s f-name)))]
    [else
     (match (first funs)
       [(FunC n p b)
        (cond
          [(symbol=? (idC-s f-name) (idC-s n)) (idC-s p)]
          [else (find-param f-name (rest funs))])])]))

;; Purpose: A helper function that searches the list of functions for the matching name, and
;; returns the expression in the body of the found function
(define (find-expr [f-name : idC] [funs : (Listof FunC)]) : ExprC
  (match (first funs)
    [(FunC n p b)
     (cond
       [(symbol=? (idC-s f-name) (idC-s n)) b]
       [else (find-expr f-name (rest funs))])]))

;; Purpose: The main interpreter that interprets a whole program by taking in
;; a list of s-exps and interpreting them to return the program's value (a real number)
(define (top-interp (fun-sexps : Sexp)) : Real
  (interp-fns (parse-prog fun-sexps)))

;; Purpose: Interprets the functions in the program by calling the 'main' function with arg 0
;; Testing at bottom of program using top-interp
(define (interp-fns (funs : (Listof FunC))) : Real
  (interp (appC (find-func (idC 'main) funs) (NumC 0)) funs))

;; -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
;; Parsers and helper functions

;; Purpose: Parses a given Sexp into the ExprC language
(define (parse (s : Sexp)) : ExprC
  (match s
    [(? real? n) (NumC n)]
    [(list s l r) (binopC (match s
                            [(or '+ '- '* '/) s]
                            [other (error 'parse "(PAIG) illegal operator: ~e" s)])
                          (parse l) (parse r))]
    [(list (? symbol? s) (list e)) (appC (id-parse s) (parse e))]
    [(list 'ifleq0? c ': r 'else: else) (ifleq0? (parse c) (parse r) (parse else))]
    [(or (list (? symbol? s)) (? symbol? s)) (id-parse s)]
    [other (error 'parse "(PAIG) invalid syntax: ~e" other)]))

;; Purpose: A helper function for parse that ensures a symbol input
;; returns an idC and not an ExprC for typing purposes
(define (id-parse [s : Sexp]) : idC
  (match s
    [(? symbol? s)
     (match s
       [(or '+ '- '* '/ 'fun 'ifleq0? ': 'else:) (error 'parse "(PAIG) invalid identifier: ~e" s)]
       [other (idC other)])]))

;; Purpose: Parses a function definition from a S-exp to our function-def struct,
;; giving it an idC name, idC parameter, and expression in the body
(define (parse-fundef (s : Sexp)) : FunC
  (match s
    [(list 'fun (list name (list param)) body)
     (FunC (id-parse name) (id-parse param) (parse body))]
    [other (error 'parse-fundef "(PAIG) illegal function definition: ~e" other)]))

;; Purpose: Parses the program to create a list of functions written in the program
(define (parse-prog (s : Sexp)) : (Listof FunC)
  (match s
    ['() '()] ; If there are no function definitions, return an empty list.
    [(cons defn rest) (cons (parse-fundef defn) (parse-prog rest))])) ; Recursively parse each definition.

;; -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
;; Test Cases

;; interp tests
(define prog1 (parse-prog '{{fun {f (x)} {* x 2}}
                            {fun {g (y)} (+ y 5)}}))
(check-equal? (interp (parse '{f ({g(20)})}) prog1) 50)
(check-equal? (interp (parse '{f (30)}) prog1) 60)
(check-equal? (interp (parse '{g (10)}) prog1) 15)

;; subst tests
(check-equal? (subst (NumC 10) 'x (binopC '+ (idC 'x) (NumC 2)))
              (binopC '+ (NumC 10) (NumC 2)))
(check-equal? (subst (NumC 10) 'x (ifleq0? (idC' x) (idC 'x) (NumC 2)))
              (ifleq0? (NumC 10) (NumC 10) (NumC 2)))
(check-equal? (subst (idC 'y) 'x (binopC '+ (idC 'x) (NumC 2)))
              (binopC '+ (idC 'y) (NumC 2)))
(check-equal? (subst (NumC 10) 'x (appC (idC 'f) (appC (idC 'g) (idC 'x))))
              (appC (idC 'f) (appC (idC 'g) (NumC 10))))

;; find-expr tests
(check-equal? (find-expr (idC 'f) (list (FunC (idC 'f) (idC 'x) (NumC 2)))) (NumC 2))
(check-equal? (find-expr (idC 'g) (list (FunC (idC 'f) (idC 'x) (NumC 2))
                                        (FunC (idC 'g) (idC 'y) (NumC 3)))) (NumC 3))
(check-equal? (find-expr (idC 'h) (list (FunC (idC 'f) (idC 'x) (NumC 2))
                                        (FunC (idC 'g) (idC 'y) (NumC 3))
                                        (FunC (idC 'h) (idC 'z) (NumC 4)))) (NumC 4))

;; find-param tests
(check-equal? (find-param (idC 'f) (list (FunC (idC 'f) (idC 'x) (NumC 2)))) 'x)
(check-equal? (find-param (idC 'g) (list (FunC (idC 'f) (idC 'x) (NumC 2))
                                         (FunC (idC 'g) (idC 'y) (NumC 3)))) 'y)
(check-equal? (find-param (idC 'h) (list (FunC (idC 'f) (idC 'x) (NumC 2))
                                         (FunC (idC 'g) (idC 'y) (NumC 3))
                                         (FunC (idC 'h) (idC 'z) (NumC 4)))) 'z)

;; find-func tests
(check-equal? (find-func (idC 'f) (list (FunC (idC 'f) (idC 'x) (NumC 2)))) (idC 'f))
(check-equal? (find-func (idC 'g) (list (FunC (idC 'f) (idC 'x) (NumC 2))
                                        (FunC (idC 'g) (idC 'y) (NumC 3)))) (idC 'g))
(check-equal? (find-func (idC 'h) (list (FunC (idC 'f) (idC 'x) (NumC 2))
                                        (FunC (idC 'g) (idC 'y) (NumC 3))
                                        (FunC (idC 'h) (idC 'z) (NumC 4)))) (idC 'h))

;; parse-prog tests
(define prog2 '{{fun {f (x)} {* x 2}}
                {fun {g (y z)} (+ y z)}})
(define prog3 '{{fun {f (x)} {* x 2}}
                {fun {g (+)} (+ y z)}})
(check-equal? (parse-prog
               '{{fun {f1 (x)} {+ x 1}} {fun {f2 (y)} {* y 2}}})
              (list (FunC (idC 'f1) (idC 'x) (binopC '+ (idC 'x) (NumC 1)))
                    (FunC (idC 'f2) (idC 'y) (binopC '* (idC 'y) (NumC 2)))))
(check-equal? (parse-prog '{{fun {f (x)} {f2 (2)}}})
              (list (FunC (idC 'f) (idC 'x) (appC (idC 'f2) (NumC 2)))))
(check-exn (regexp (regexp-quote "parse-fundef: (PAIG) illegal function definition: '(fun (g (y z)) (+ y z))"))
           (lambda () (parse-prog prog2)))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '+"))
           (lambda () (parse-prog prog3)))

;; parse fun-def tests
(check-equal? (parse-fundef '{fun {double (x)} {* x 2}})
              (FunC (idC 'double) (idC 'x) (binopC '* (idC 'x) (NumC 2))))
(check-equal? (parse-fundef '{fun {give (x)} x})
              (FunC (idC 'give) (idC 'x) (idC 'x)))
(check-equal? (parse-fundef '{fun {cube (x)} {* x {* x x}}})
              (FunC (idC 'cube) (idC 'x) (binopC '* (idC 'x) (binopC '* (idC 'x) (idC 'x)))))
(check-exn (regexp (regexp-quote "parse-fundef: (PAIG) illegal function definition: '(fun (f (x y)) (+ 1 2))"))
           (lambda () (parse-fundef '{fun {f (x y)} {+ 1 2}})))

;; Parsing tests
(check-equal? (parse '{+ 1 2}) (binopC '+ (NumC 1) (NumC 2)))
(check-equal? (parse '{f (2)}) (appC (idC 'f) (NumC 2)))
(check-equal? (parse '{* 1 x}) (binopC '* (NumC 1) (idC 'x)))
(check-equal? (parse '{ifleq0? x : x else: {- x 1}})
              (ifleq0? (idC 'x) (idC 'x) (binopC '- (idC 'x) (NumC 1))))
(check-equal? (parse '{f ({g (2)})}) (appC (idC 'f) (appC (idC 'g) (NumC 2))))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid syntax: '(one too many things)"))
           (lambda () (parse '{one too many things})))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '+"))
           (lambda () (parse '+)))

;; id-parse tests
(check-equal? (id-parse 'x) (idC 'x))
(check-equal? (id-parse '=) (idC '=))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '+"))
           (lambda () (id-parse '+)))

;; Multiple test including program implementation, init value, nested calls, error checks, etc
(check-equal? (top-interp '{{fun {f (x)} {+ x 14}}
                            {fun {main (init)} {f (2)}}}) 16)

(check-equal? (top-interp '{{fun {f (x)} {/ x 2}}
                            {fun {g (y)} {* y 4}}
                            {fun {main (init)} {+ (f (10)) (g (5))}}}) 25)

(check-equal? (top-interp '{{fun {f (x)} {* x 10}}
                            {fun (g (y)) {+ y 5}}
                            {fun {main (init)} {f ({g (init)})}}}) 50)

(check-equal? (top-interp '{{fun {f (x)} {* x 10}}
                            {fun {sub1 (y)} {- y 1}}
                            {fun (start (z)) {+ z 5}}
                            {fun {main (init)}
                                 {ifleq0? (start (init)) : (f (2)) else: (f ({sub1 (init)}))}}}) -10)

(check-equal? (top-interp '{{fun {f (x)} {* x 10}}
                            {fun {sub1 (y)} {- y 1}}
                            {fun (start (z)) {+ z 5}}
                            {fun {main (init)}
                                 {ifleq0? (sub1 (init)) : (f (2)) else: (f ({sub1 (init)}))}}}) 20)

(check-exn (regexp (regexp-quote "find-func: (PAIG) Function {main} not defined"))
           (lambda () (top-interp '{{fun {f (x)} {* x 10}}
                                    {fun {sub1 (y)} {- y 1}}
                                    {fun (start (z)) {+ z 5}}})))

(check-exn (regexp (regexp-quote "find-param: (PAIG) Function {e} not defined"))
           (lambda () (top-interp '{{fun {f (x)} {* x 10}}
                                    {fun (g (y)) {+ y 5}}
                                    {fun {main (init)} {f ({e (init)})}}})))

(check-exn (regexp (regexp-quote "subst: (PAIG) Unbound identifier: 'z"))
           (lambda () (top-interp '{{fun {f (x)} {* x 10}}
                                    {fun (g (y)) {+ z 5}}
                                    {fun {main (init)} {f ({g (init)})}}})))

(check-exn (regexp (regexp-quote "parse: (PAIG) illegal operator: '^"))
           (lambda () (top-interp '{{fun {f (x)} {^ x 10}}
                                    {fun (g (y)) {+ y 5}}
                                    {fun {main (init)} {f ({g (init)})}}})))

(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: ':"))
           (lambda () (top-interp '{{fun {f (:)} {+ x 10}}
                                    {fun (g (y)) {+ y 5}}
                                    {fun {main (init)} {f ({g (init)})}}})))

(check-exn (regexp (regexp-quote "eval: (PAIG) cannot divide by zero"))
           (lambda () (top-interp '((fun (ignoreit (x)) (+ 3 4))
                                    (fun (main (init)) (ignoreit ((/ 1 (+ 0 0)))))))))