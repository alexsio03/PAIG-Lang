#lang typed/racket

;; Project fully implemented, all tests passed

(require typed/rackunit)

;; ExprC struct definitions
(define-type ExprC (U numC idC strC ifC blamC appC))
(struct numC ([n : Real]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct strC ([str : String]) #:transparent)
(struct ifC ([check : ExprC] [true : ExprC] [false : ExprC]) #:transparent)
(struct blamC ([params : (Listof idC)] [body : ExprC]) #:transparent)
(struct appC ([func : ExprC] [args : (Listof ExprC)]) #:transparent)

;; Value struct definitions
(define-type Value (U numV closV strV boolV primopV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct strV ([str : String]) #:transparent)
(struct closV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([op : Symbol] [arity : Real] [env : Env]) #:transparent)

;; Binding/Env definitions
(struct Binding ([key : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof Binding))

;; STRUCTURE OF ASGN5
;; 1. parse takes in S-expression and returns an ExprC
;; 2. interp takes in ExprC and returns a Value
;; 3. serialize takes in a Value and returns a string

; The top environment with primop bindings
(define (create-top-env) : Env
  (list
   (Binding 'true (boolV true))
   (Binding 'false (boolV false))
   (Binding '+ (primopV '+ 2 '()))
   (Binding '* (primopV '* 2 '()))
   (Binding '- (primopV '- 2 '()))
   (Binding '/ (primopV '/ 2 '()))
   (Binding '<= (primopV '<= 2 '()))
   (Binding 'equal? (primopV 'equal? 2 '()))
   (Binding 'error (primopV 'error 1 '()))))

(define top-env (create-top-env))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; parser and helper functions

; Purpose: Takes in an s-expression and parses it into an ExprC type
(define (parse (s : Sexp)) : ExprC
  (match s
    [(? real? n) (numC n)]
    [(? symbol? s) (check-sym s)]
    [(? string? str) (strC str)]
    [(list c '? t 'else: f) (ifC (parse c) (parse t) (parse f))];ifC
    [(list 'blam (list p ...) b) (blamC (check-dupes ((inst map idC Sexp) parse-params p))
                                        (parse b))];blamC
    [(list 'with subs ... ': func) 
     (appC (blamC (check-dupes ((inst map idC Any) get-var subs)) (parse func))
           ((inst map ExprC Any) get-val subs))]
    [(list func1 func2 ...) (appC (parse func1) ((inst map ExprC Sexp) parse func2))]));appC

; Purpose: A helper function for the parser which takes in a list of idC's and makes sure
; each idC only appears once. Errors if there is a duplicate, returns the list of not.
(define (check-dupes (lst : (Listof idC))) : (Listof idC)
  (match lst
    ['() '()]
    [(cons f r)
     (match (member f r)
       [#f (cons f (check-dupes r))]
       [else (error 'check-dupes "(PAIG) Duplicate identifier: ~v" (idC-s f))])]))

; Purpose: A helper function for the parser which takes in a symbol and makes sure it is
; not a restricted symbol. Errors on failure, return's an idC with given symbol on success.
(define (check-sym (s : Symbol)) : idC
  (match s
       [(or '? 'with 'as 'blam 'else:) (error 'parse "(PAIG) invalid identifier: ~e" s)]
       [other (idC other)]))

; Purpose: A helper function for the parser which takes in a [val as var] from a 'with'
; statement, and returns the var as an idC
(define (get-var (s : Any)) : idC
  (match s
    [(list val 'as (? symbol? var)) (check-sym var)]))

; Purpose: A helper function for the parser which takes in a [val as var] from a 'with'
; statement, and returns a parsed version of the val
(define (get-val (s : Any)) : ExprC
  (match s
    [(list val 'as (? symbol? var)) (parse (cast val Sexp))]))

; Purpose: A helper function for the parser which takes in an s-expression from the 'blam'
; and ensures all parameters passed were symbols
(define (parse-params (s : Sexp)) : idC
  (match s
    [(? symbol? s) (check-sym s)]
    [other (error 'parse-params "(PAIG) Parameters must be symbols, given: ~v" s)]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; interpreters and helper functions

; Purpose: The main interpreter of the PAIG language which takes in an ExprC type and an
; environment with bindings, and interprets the ExprC into a Value
(define (interp (e : ExprC) (env : Env)) : Value
  (match e
    [(numC n) (numV n)]
    [(strC str) (strV str)]
    [(idC s) (lookup s env)]
    [(ifC c t f)
     (match (interp c env)
       [(boolV b)
        (match b
          [#t (interp t env)]
          [#f (interp f env)])]
       [other (error 'interp "(PAIG) first arg in if must be a boolean:~n~e" c)])]
    [(blamC params b) (closV ((inst map Symbol idC) idC-s params) b env)]
    [(appC f vals)
     (match (interp f env)
       [(closV params body e) (interp body (append (bind params
                                            ((inst map Value ExprC) (λ (x) (interp x env)) vals)) e))]
       [(primopV op ar e)
        (cond
          [(and (equal? ar 2) (equal? ar (length vals)))
           (eval (primopV op ar env) (interp (first vals) env) (interp (second vals) env))]
          [(and (equal? ar 1) (equal? ar (length vals)))
           (match op
             ['error (error 'user-error 
                            (match (first vals)
                              [(idC s) (format "~v" s)]
                              [other (serialize (interp other env))]))])]
          [else (error 'interp "(PAIG) Wrong number of arguments: expected ~e, got ~e" ar (length vals))])]
       [other (error 'interp "(PAIG) invalid function: ~v" f)])]))

; Purpose: A helper function used to evalueate primitive operators, which takes in a primopV as well
; as two arguments, and interprets the whole expression into a Value based on the primop's identifier
(define (eval (prim : primopV) (arg1 : Value) (arg2 : Value)) : Value
  (cond
    [(and (numV? arg1) (numV? arg2))
     (match (primopV-op prim)
       ['+ (numV (+ (numV-n arg1) (numV-n arg2)))]
       ['* (numV (* (numV-n arg1) (numV-n arg2)))]
       ['- (numV (- (numV-n arg1) (numV-n arg2)))]
       ['/
        (match arg2
          [(numV 0) (error 'eval "(PAIG) Cannot divide by zero")]
          [other (numV (/ (numV-n arg1) (numV-n arg2)))])]
       ['<= (boolV (<= (numV-n arg1) (numV-n arg2)))]
       ['equal? (boolV (equal? (numV-n arg1) (numV-n arg2)))])]
    [(equal? (primopV-op prim) 'equal?)
     (cond
       [(and (boolV? arg1) (boolV? arg2)) (boolV (equal? (boolV-b arg1) (boolV-b arg2)))]
       [(and (strV? arg1) (strV? arg2)) (boolV (equal? (strV-str arg1) (strV-str arg2)))]
       [else (boolV #f)])]
    [else (error 'eval "(PAIG) invalid syntax for: ~v" (primopV-op prim))]))

; Purpose: A helper function which takes a list of parameters and values, and returns a list of
; Binding types with each parameter at index i bound to each value at index i of either list
(define (bind (params : (Listof Symbol)) (vals : (Listof Value))) : (Listof Binding) 
  (match (equal? (length params) (length vals))
    [#t
     (match params
       ['() '()]
       [(cons f r) (cons (Binding f (first vals)) (bind r (rest vals)))])]
    [#f (error 'bind "(PAIG) expected ~v values, got ~v" (length params) (length vals))]))

; Purpose: A helper function which takes in a symbol and an environment and searches the environment.
; If the symbol is found, it returns the value bound to that symbol in the environment, else it errors
(define (lookup [var : Symbol] [env : Env]) : Value
  (match env
    ['() (error 'lookup "(PAIG) unbound identifier: ~e" var)]
    [other (cond
             [(symbol=? var (Binding-key (first env)))
              (Binding-val (first env))]
             [else (lookup var (rest env))])]))

; Purpose: The top-interp function which takes in an s-expression and returns the evaluated and serialized
; program in a String
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; serialize

; Purpose: The serialize function which takes in a Value and returns the serialized version of that
; value as a String
(define (serialize (v : Value)) : String
  (match v
    [(numV n) (format "~v" n)]
    [(boolV b)
     (match b
       [#t "true"]
       [#f "false"])]
    [(strV str) (format "~v" str)]
    [(closV prms b e) "#<procedure>"]
    [(primopV op ar e) "#<primop>"]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; tests

; parse tests
(check-equal? (parse '{with : {+ 2 2}}) (appC (blamC '() (appC (idC '+) (list (numC 2) (numC 2)))) '()))
(check-equal? (parse '{with [{blam {x} {blam {y} {+ x y}}} as f] : {{f 3} 7}})
              (appC
               (blamC (list (idC 'f)) (appC (appC (idC 'f) (list (numC 3))) (list (numC 7))))
               (list (blamC (list (idC 'x)) (blamC (list (idC 'y)) (appC (idC '+) (list (idC 'x) (idC 'y))))))))
(check-equal? (parse '{with [5 as x] [7 as y] : {+ x y}})
              (appC (blamC (list (idC 'x) (idC 'y)) (appC (idC '+) (list (idC 'x) (idC 'y)))) (list (numC 5) (numC 7))))
(check-equal? (parse '{{blam {} 100}}) (appC (blamC '() (numC 100)) '()))
(check-equal? (parse '{blam {x y} {+ x y}}) (blamC (list (idC 'x) (idC 'y)) (appC (idC '+) (list (idC 'x) (idC 'y)))))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '?"))
           (lambda () (parse '{? 2 3})))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '?"))
           (lambda () (parse '{blam {} {? 2 3}})))
(check-exn (regexp (regexp-quote "check-dupes: (PAIG) Duplicate identifier: 'x"))
           (lambda () (parse '(blam (x x) 3))))
(check-exn (regexp (regexp-quote "parse-params: (PAIG) Parameters must be symbols, given: 2"))
           (lambda () (parse '(blam (2 3 4) 6))))
(check-exn (regexp (regexp-quote "check-dupes: (PAIG) Duplicate identifier: 'z"))
           (lambda () (parse '(with ((blam () 3) as z) (9 as z) : (z)))))

; interp tests
(check-equal? (interp (parse '{{blam {compose add1}
                                     {{blam {add2} {add2 99}}
                                      {compose add1 add1}}}
                               {blam {f g} {blam {x} {f {g x}}}}
                               {blam {x} {+ x 1}}}) top-env) (numV 101))
(check-equal? (interp (parse '{{{blam {f g} {blam {x} {f {g x}}}}
                                {blam {x} {+ x 1}} {blam {x} {* x 2}}} 10}) top-env) (numV 21))
(check-equal? (interp (parse '{{blam {x y} {+ x y}} 2 3}) top-env) (numV 5))
(check-exn (regexp (regexp-quote "eval: (PAIG) invalid syntax for: '+"))
           (lambda () (interp (parse '{{blam {x y} {+ x y}} 2 "a"}) top-env)))
(check-equal? (interp (parse '{{blam {x} {* x 2}} 10}) top-env) (numV 20))
(check-equal? (interp (parse '{{blam {x} {- x 5}} 10}) top-env) (numV 5))
(check-exn (regexp (regexp-quote "eval: (PAIG) Cannot divide by zero"))
           (lambda () (interp (parse '{{blam {} {/ 1 0}}}) top-env)))
(check-equal? (interp (parse '{{blam {f y} {+ {f 10} y}} {blam {x} {* x 2}} 10}) top-env) (numV 30))
(check-equal? (interp (parse '{{blam {f g} {+ {f 10} (g 6)}}
                               {blam {x} {* x 2}} {blam {x} {/ x 2}}}) top-env) (numV 23))
(check-equal? (interp (parse '{{{blam {} {equal? 20 20}}} ? "20 = 20" else: "20 /= 20"}) top-env) (strV "20 = 20"))
(check-equal? (interp (parse '{{{blam {} {<= 10 2}}} ? "10 <= 2" else: "2 <= 10"}) top-env) (strV "2 <= 10"))
(check-exn (regexp (regexp-quote
                    "interp: (PAIG) first arg in if must be a boolean:
(appC (blamC '() (appC (idC '+) (list (numC 10) (numC 10)))) '())"))
           (lambda () (interp (parse '{{{blam {} {+ 10 10}}} ? "20 = 20" else: "20 /= 20"}) top-env)))
(check-equal? (interp (parse '{{blam {} {equal? "one" "one"}}}) top-env) (boolV #t))
(check-equal? (interp (parse '{{blam {} {equal? {blam {} 2} {blam {} 2}}}}) top-env) (boolV #f))
(check-equal? (interp (parse '{{blam {} {equal? 2 10}}}) top-env) (boolV #f))
(check-equal? (interp (parse '{{blam {} {equal? true true}}}) top-env) (boolV #t))
(check-exn (regexp (regexp-quote "user-error: '200!"))
           (lambda () (interp (parse '{{blam {} {error 200!}}}) top-env)))
(check-exn (regexp (regexp-quote "user-error: \"big error here\""))
           (lambda () (interp (parse '{{blam {} {error "big error here"}}}) top-env)))
(check-exn (regexp (regexp-quote "interp: (PAIG) Wrong number of arguments: expected 2, got 3"))
           (lambda () (interp (parse '{{blam {} {+ 1 2 3}}}) top-env)))
(check-exn (regexp (regexp-quote "bind: (PAIG) expected 3 values, got 2"))
           (lambda () (interp (parse '{{blam {x y z} {+ x {* y z}}} 5 10}) top-env)))
(check-exn (regexp (regexp-quote "lookup: (PAIG) unbound identifier: 'y"))
           (lambda () (interp (parse '{{blam {x} {+ x y}} 2}) top-env)))

; eval tests
(check-equal? (eval (primopV 'equal? 2 '()) (numV 2) (numV 2)) (boolV #t))
(check-equal? (eval (primopV 'equal? 2 '()) (numV 2) (numV 10)) (boolV #f))
(check-equal? (eval (primopV 'equal? 2 '()) (boolV #f) (boolV #f)) (boolV #t))
(check-equal? (eval (primopV 'equal? 2 '()) (strV "a") (strV "a")) (boolV #t))
(check-equal? (eval (primopV 'equal? 2 '()) (strV "a") (strV "b")) (boolV #f))

; serialize tests
(check-equal? (serialize (interp (parse '{{blam {x} {<= x 0}} 10}) top-env)) "false")
(check-equal? (serialize (interp (parse '{{blam {x} {<= x 0}} 0}) top-env)) "true")
(check-equal? (serialize (primopV '+ 2 '())) "#<primop>")

; top-interp tests
(check-equal? (top-interp '{{blam {x} {* x 2}} 10}) "20")
(check-equal? (top-interp '{blam {x} {* x 2}}) "#<procedure>")
(check-exn (regexp (regexp-quote "interp: (PAIG) invalid function: (numC 3)"))
           (lambda () (top-interp '{3 4 5})))
