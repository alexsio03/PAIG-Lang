#lang typed/racket

;; Project fully implemented, all tests passed

(require typed/rackunit)

;; ExprC struct definitions
(define-type ExprC (U numC idC strC ifC blamC appC setC))
(struct numC ([n : Real]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct strC ([str : String]) #:transparent)
(struct ifC ([check : ExprC] [true : ExprC] [false : ExprC]) #:transparent)
(struct blamC ([params : (Listof idC)] [body : ExprC]) #:transparent)
(struct appC ([func : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct setC ([var : idC] [expr : ExprC]) #:transparent)

;; Value struct definitions
(define-type Value (U numV closV strV boolV primopV nullV arrayV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct strV ([str : String]) #:transparent)
(struct closV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([op : Symbol] [arity : Real] [env : Env]) #:transparent)
(struct nullV () #:transparent)
(struct arrayV ([loc : Natural] [length : Natural]) #:transparent)

;; Binding/Env definitions
(struct Binding ([key : Symbol] [loc : Natural]) #:transparent)
(define-type Env (Listof Binding))

;; Store definitions
(struct Store ([vec : (Vectorof Value)]) #:transparent)

; The top environment with primop bindings
(define (create-top-env) : Env
  (list
   (Binding 'true 1)
   (Binding 'false  2)
   (Binding 'null  3)
   (Binding '+  4)
   (Binding '*  5)
   (Binding '-  6)
   (Binding '/  7)
   (Binding '<=  8)
   (Binding 'do 9)
   (Binding 'error  10)
   (Binding 'array  11)
   (Binding 'equal?  12)
   (Binding 'make-array  13)
   (Binding 'aref  14)
   (Binding 'aset! 15)
   (Binding 'substring 16)))

(define top-env (create-top-env))

(define make-value-vector (inst make-vector Value))

; Initial store with initial bindings
(define (make-initial-store (memsize : Natural)) : Store
  (define vec (make-value-vector memsize (nullV)))
  (match (< memsize 17)
    [#t (error 'initial-store "(PAIG) Not enough memory for initial bindings")]
    [#f
     (vector-set! vec 1 (boolV true))
     (vector-set! vec 2 (boolV false))
     (vector-set! vec 3 (nullV))
     (vector-set! vec 4 (primopV '+ 2 '()))
     (vector-set! vec 5 (primopV '* 2 '()))
     (vector-set! vec 6 (primopV '- 2 '()))
     (vector-set! vec 7 (primopV '/ 2 '()))
     (vector-set! vec 8 (primopV '<= 2 '()))
     (vector-set! vec 9 (primopV 'do 1 '()))
     (vector-set! vec 10 (primopV 'error 1 '()))
     (vector-set! vec 11 (primopV 'array 1 '()))
     (vector-set! vec 12 (primopV 'equal? 2 '()))
     (vector-set! vec 13 (primopV 'make-array 2 '()))
     (vector-set! vec 14 (primopV 'aref 2 '()))
     (vector-set! vec 15 (primopV 'aset! 3 '()))
     (vector-set! vec 16 (primopV 'substring 3 '()))
     (vector-set! vec 0 (numV 17))
     (Store vec)]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; interpreters and helper functions

; Purpose: The main interpreter of the PAIG language which takes in an ExprC type and an
; environment with bindings, and interprets the ExprC into a Value
(define (interp (e : ExprC) (env : Env) (sto  : Store)) : Value
  (match e
    [(numC n) (numV n)]
    [(strC str) (strV str)]
    [(idC s) (fetch (lookup s env) sto)]
    [(setC id val)
     (match (lookup (idC-s id) env)
       [(? natural? n) (store-loc-set! sto n (interp val env sto))])]
    [(ifC c t f)
     (match (interp c env sto)
       [(boolV b)
        (match b
          [#t (interp t env sto)]
          [#f (interp f env sto)])]
       [other (error 'interp "(PAIG) first arg in if must be a boolean:~n~e" c)])]
    [(blamC params b) (closV ((inst map Symbol idC) idC-s params) b env)]
    [(appC f vals)
     (match (interp f env sto)
       [(closV params body e)
        (interp body (append (bind params
                                   ((inst map Value ExprC) (λ (x) (interp x env sto)) vals) sto) e) sto)]
       [(primopV op ar e)
        (cond
          [(and (equal? ar 3) (equal? ar (length vals)))
           (match op
             ['aset! (arr-set (interp (first vals) env sto)
                              (interp (second vals) env sto) (interp (third vals) env sto) sto)]
             ['substring (strV (substr (interp (first vals) env sto) (interp (second vals) env sto)
                                       (interp (third vals) env sto)))])]
          [(and (equal? ar 2) (equal? ar (length vals)))
           (match op
             [(or '+ '- '* '/ '<= 'equal?)
              (eval (primopV op ar env) (interp (first vals) env sto) (interp (second vals) env sto))]
             ['make-array
              (match (interp (first vals) env sto)
                [(numV n)
                 (match (< n 1)
                   [#f
                    (match n
                      [(? natural? num)
                       (begin
                         (define arr (make-arr num (interp (second vals) env sto)))
                         (define loc (put sto (first arr)))
                         ((inst map Natural Value) (λ (x) (put sto x)) (rest arr))
                         (arrayV loc (length arr)))]
                      [other (error 'make-array "(PAIG) Size must be integer, not: ~v" n)])]
                   [#t (error 'make-array "(PAIG) Cannot make array with less than one cell")])]
                [other (error 'make-array "(PAIG) First arg must be a number in make-array")])]
             ['aref (arr-find (interp (first vals) env sto) (interp (second vals) env sto) sto)])]
          [else
           (match op
             ['error (error 'user-error
                            (match (first vals)
                              [(idC s) (format "~v" s)]
                              [other (serialize (interp other env sto))]))]
             ['do (define list ((inst map Value ExprC) (λ (x) (interp x env sto)) vals)) (last list)]
             ['array
              (match (< (length vals) 1)
                [#f
                 (begin
                   (define arr ((inst map Value ExprC) (λ (x) (interp x env sto)) vals))
                   (define loc (put sto (first arr)))
                   ((inst map Natural Value) (λ (x) (put sto x)) (rest arr))
                   (arrayV loc (length arr)))]
                [#t (error 'array "(PAIG) Array must have at least one cell")])]
             [other (error 'interp "(PAIG) Wrong number of arguments: expected ~e, got ~e for ~e"
                           ar (length vals) op)])])]
       [other (error 'interp "(PAIG) invalid function: ~v" f)])]))

; Purpose: Takes in a string, a start index, and an end index, and returns
; the string from index start to index end.
(define (substr (str : Value) (start : Value) (end : Value)) : String
  (cond
    [(and (strV? str) (numV? start) (numV? end))
     (cond
       [(and (natural? (numV-n start)) (natural? (numV-n end)))
        (substring (strV-str str) (numV-n start) (numV-n end))]
       [else (error 'substring "(PAIG) indexes must be natural numbers")])]
    [else (error 'substring "(PAIG) arguments were wrong types")]))

; Purpose: Takes in an array, an index, a value, and a store, and performs the operation
; array[index] = value. Returns null
(define (arr-set (arr : Value) (index : Value) (val : Value) (sto : Store)) : nullV
  (match index
    [(numV n)
     (match n
       [(? natural? n)
        (match arr
          [(arrayV loc len)
           (match (> n (- len 1))
             [#f (store-loc-set! sto (+ loc n) val)]
             [#t (error 'aset! "(PAIG) Index ~e out of bounds for array" n)])]
          [other (error 'aset! "(PAIG) Array must be array type, given ~e" arr)])]
       [other (error 'aset! "(PAIG) index must be a natural number")])]
    [other (error 'aset! "(PAIG) index must be a number")])
  (nullV))

; Purpose: Takes in a size and a value, and returns a list of values
; of given size filled with the given value
(define (make-arr (size : Integer) (el : Value)) : (Listof Value)
  (match size
    [0 '()]
    [other (cons el (make-arr (sub1 size) el))]))

; Purpose: Takes in an array, an index, and a store. Returns the value
; at the given index in the array.
(define (arr-find (arr : Value) (index : Value) (sto : Store)) : Value
  (match index
    [(numV n)
     (match n
     [(? natural?)
      (match arr
          [(arrayV loc len)
           (match (> n (- len 1))
             [#f (fetch (+ loc n) sto)]
             [#t (error 'aref "(PAIG) Index ~e out of bounds for array" n)])])]
     [other (error 'aref "(PAIG) index must be a natural number")])]
    [other (error 'aref "(PAIG) index must be a number")]))

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
(define (bind (params : (Listof Symbol)) (vals : (Listof Value)) (sto : Store)) : (Listof Binding)
  (match (equal? (length params) (length vals))
    [#t
     (match params
       ['() '()]
       [(cons f r)
        (match (put sto (first vals))
          [(? natural? n)
           (match n
             [(? natural? n) (cons (Binding f n) (bind r (rest vals) sto))])])])]
    [#f (error 'bind "(PAIG) expected ~v values, got ~v" (length params) (length vals))]))

; Purpose: A helper function which takes in a symbol and an environment and searches the environment.
; If the symbol is found, it returns the location bound to that symbol in the environment, else it errors
(define (lookup [var : Symbol] [env : Env]) : Natural
  (match env
    ['() (error 'lookup "(PAIG) unbound identifier: ~e" var)]
    [other (cond
             [(symbol=? var (Binding-key (first env)))
              (Binding-loc (first env))]
             [else (lookup var (rest env))])]))

;; Purpose: Takes in a location and a store and returns the value at that location
(define (fetch [loc : Natural] [sto : Store]) : Value
  (vector-ref (Store-vec sto) loc))

; Purpose: Takes in a store, a location, and a value, and sets value at that location
; to the given value. Return null
(define (store-loc-set! (sto : Store) (loc : Natural) (val : Value)) : nullV
  (vector-set! (Store-vec sto) loc val)
  (nullV))

;; Purpose: Takes in a value and adds it to the next available spot in the store.
;; Returns the location where the value was added.
(define (put (sto : Store) (val : Value)) : Natural
  (define first (vector-ref (Store-vec sto) 0))
  (match first
    [(numV first)
     (match (> (+ 1 first) (vector-length (Store-vec sto)))
       [#f
        (match first
          [(? natural? first)
           (begin
             (vector-set! (Store-vec sto) first val)
             (vector-set! (Store-vec sto) 0 (numV (+ 1 first)))
             first)])]
       [#t (error 'put "(PAIG) Out of memory")])]))

; Purpose: The top-interp function which takes in an s-expression and returns the evaluated and serialized
; program in a String
(define (top-interp [s : Sexp] [memsize : Natural]) : String
  (serialize (interp (parse s) top-env (make-initial-store memsize))))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; serialize

; Purpose: The serialize function which takes in a Value and returns the serialized version of that
; value as a String
(define (serialize (v : Value)) : String
  (match v
    [(nullV) "null"]
    [(numV n) (format "~v" n)]
    [(boolV b)
     (match b
       [#t "true"]
       [#f "false"])]
    [(strV str) (format "~v" str)]
    [(closV prms b e) "#<procedure>"]
    [(primopV op ar e) "#<primop>"]
    [(arrayV loc len) "#<array>"]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; parser and helper functions

; Purpose: Takes in an s-expression and parses it into an ExprC type
(define (parse (s : Sexp)) : ExprC
  (match s
    ['() (error 'parse "(PAIG) Cannot parse empty list")]
    [(? real? n) (numC n)]
    [(? symbol? s) (check-sym s)]
    [(? string? str) (strC str)]
    [(list (? symbol? var) ':= expr) (setC (check-sym var) (parse expr))]
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
    [(or ':= '? 'with 'as ': 'blam 'else:) (error 'parse "(PAIG) invalid identifier: ~e" s)]
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

; The while function written as a recursive s-expression
(define while '{blam {self guard body}
             {{guard} ? {do {body}
                            {self self guard body}}
                      else: null}})

; The in-order function that takes in an array and length of array, and returns true
; if the array is in increasing order
(define in-order
  '{blam (arr n) {with [{- n 1} as index] [0 as count] :
                   {do {while while
                    {blam {} {<= 1 index}}
                    {blam {} {do {{<= {aref arr {- index 1}}
                                      {aref arr index}} ? {count := {+ 1 count}} else: null} {index := {- index 1}}}}}
                     {equal? count {- n 1}}}}})

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; tests

; parse tests
(check-equal? (parse '{with : {+ 2 2}}) (appC (blamC '() (appC (idC '+) (list (numC 2) (numC 2)))) '()))
(check-equal? (parse '{with [{blam {x} {blam {y} {+ x y}}} as f] : {{f 3} 7}})
              (appC
               (blamC (list (idC 'f)) (appC (appC (idC 'f) (list (numC 3))) (list (numC 7))))
               (list (blamC (list (idC 'x)) (blamC (list (idC 'y))
                                                   (appC (idC '+) (list (idC 'x) (idC 'y))))))))
(check-equal? (parse '{with [5 as x] [7 as y] : {+ x y}})
              (appC (blamC (list (idC 'x) (idC 'y)) (appC (idC '+) (list (idC 'x) (idC 'y))))
                    (list (numC 5) (numC 7))))
(check-equal? (parse '{{blam {} 100}}) (appC (blamC '() (numC 100)) '()))
(check-equal? (parse '{blam {x y} {+ x y}}) (blamC (list (idC 'x) (idC 'y))
                                                   (appC (idC '+) (list (idC 'x) (idC 'y)))))
(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '?"))
           (lambda () (parse '{? 2 3})))
(check-exn (regexp (regexp-quote "parse: (PAIG) Cannot parse empty list"))
           (lambda () (parse '{})))
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
                               {blam {x} {+ x 1}}}) top-env (make-initial-store 25)) (numV 101))
(check-equal? (interp (parse '{{{blam {f g} {blam {x} {f {g x}}}}
                                {blam {x} {+ x 1}} {blam {x} {* x 2}}} 10}) top-env (make-initial-store 25)) (numV 21))
(check-equal? (interp (parse '{{blam {x y} {+ x y}} 2 3}) top-env (make-initial-store 25)) (numV 5))
(check-exn (regexp (regexp-quote "eval: (PAIG) invalid syntax for: '+"))
           (lambda () (interp (parse '{{blam {x y} {+ x y}} 2 "a"}) top-env (make-initial-store 25))))
(check-equal? (interp (parse '{{blam {x} {* x 2}} 10}) top-env (make-initial-store 25)) (numV 20))
(check-equal? (interp (parse '{{blam {x} {- x 5}} 10}) top-env (make-initial-store 25)) (numV 5))
(check-exn (regexp (regexp-quote "eval: (PAIG) Cannot divide by zero"))
           (lambda () (interp (parse '{{blam {} {/ 1 0}}}) top-env (make-initial-store 25))))
(check-equal? (interp (parse '{{blam {f y} {+ {f 10} y}} {blam {x} {* x 2}} 10}) top-env
                      (make-initial-store 25)) (numV 30))
(check-equal? (interp (parse '{{blam {f g} {+ {f 10} (g 6)}}
                               {blam {x} {* x 2}} {blam {x} {/ x 2}}}) top-env
                                                                       (make-initial-store 25)) (numV 23))
(check-equal? (interp (parse '{{{blam {} {equal? 20 20}}} ? "20 = 20" else: "20 /= 20"})
                      top-env (make-initial-store 25)) (strV "20 = 20"))
(check-equal? (interp (parse '{{{blam {} {<= 10 2}}} ? "10 <= 2" else: "2 <= 10"})
                      top-env (make-initial-store 25)) (strV "2 <= 10"))
(check-exn (regexp (regexp-quote
                    "interp: (PAIG) first arg in if must be a boolean:
(appC (blamC '() (appC (idC '+) (list (numC 10) (numC 10)))) '())"))
           (lambda () (interp (parse '{{{blam {} {+ 10 10}}} ? "20 = 20" else: "20 /= 20"})
                              top-env (make-initial-store 25))))
(check-equal? (interp (parse '{{blam {} {equal? "one" "one"}}}) top-env (make-initial-store 25)) (boolV #t))
(check-equal? (interp (parse '{{blam {} {equal? {blam {} 2} {blam {} 2}}}}) top-env (make-initial-store 25)) (boolV #f))
(check-equal? (interp (parse '{{blam {} {equal? 2 10}}}) top-env (make-initial-store 25)) (boolV #f))
(check-equal? (interp (parse '{{blam {} {equal? true true}}}) top-env (make-initial-store 25)) (boolV #t))
(check-exn (regexp (regexp-quote "user-error: '200!"))
           (lambda () (interp (parse '{{blam {} {error 200!}}}) top-env (make-initial-store 25))))
(check-exn (regexp (regexp-quote "user-error: \"big error here\""))
           (lambda () (interp (parse '{{blam {} {error "big error here"}}}) top-env (make-initial-store 25))))
(check-exn (regexp (regexp-quote "interp: (PAIG) Wrong number of arguments: expected 2, got 3"))
           (lambda () (interp (parse '{{blam {} {+ 1 2 3}}}) top-env (make-initial-store 25))))
(check-exn (regexp (regexp-quote "bind: (PAIG) expected 3 values, got 2"))
           (lambda () (interp (parse '{{blam {x y z} {+ x {* y z}}} 5 10}) top-env (make-initial-store 25))))
(check-exn (regexp (regexp-quote "lookup: (PAIG) unbound identifier: 'y"))
           (lambda () (interp (parse '{{blam {x} {+ x y}} 2}) top-env (make-initial-store 25))))

; make-array tests
(check-equal?
 (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 5 2}} 23) "10")
(check-exn (regexp (regexp-quote "make-array: (PAIG) First arg must be a number in make-array"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array "test" 2}} 23)))
(check-exn (regexp (regexp-quote "make-array: (PAIG) Cannot make array with less than one cell"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 0 2}} 23)))
(check-exn (regexp (regexp-quote "make-array: (PAIG) Size must be integer, not: 1.2"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 1.2 2}} 23)))

; array tests
(check-equal?
 (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {array 1 2 3 4}} 22) "10")
(check-exn (regexp (regexp-quote "array: (PAIG) Array must have at least one cell"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {array}} 22)))

; aset! tests
(check-exn (regexp (regexp-quote "aset!: (PAIG) Index 6 out of bounds for array"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 6 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 5 2}} 23)))
(check-exn (regexp (regexp-quote "aset!: (PAIG) Array must be array type, given (strV \"not array\")"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 6 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               "not array"} 23)))
(check-exn (regexp (regexp-quote "aset!: (PAIG) index must be a natural number"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2.5 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 5 2}} 23)))
(check-exn (regexp (regexp-quote "aset!: (PAIG) index must be a number"))
           (lambda () (top-interp '{{blam {x} {do {aset! x "not num" 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 5 2}} 23)))

; aref tests
(check-exn (regexp (regexp-quote "aref: (PAIG) Index 6 out of bounds for array"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 6} 5} {aref x 1}}}}
               {make-array 5 2}} 23)))
(check-exn (regexp (regexp-quote "aref: (PAIG) index must be a natural number"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2.5} 5} {aref x 1}}}}
               {make-array 5 2}} 23)))
(check-exn (regexp (regexp-quote "aref: (PAIG) index must be a number"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x "not num"} 5} {aref x 1}}}}
               {make-array 5 2}} 23)))

; substring tests
(check-equal? (top-interp '{substring "hello world" 6 11} 20) "\"world\"")
(check-exn (regexp (regexp-quote "substring: (PAIG) arguments were wrong types"))
           (lambda () (top-interp '{substring "hello world" "wrong" 11} 20)))
(check-exn (regexp (regexp-quote "substring: (PAIG) indexes must be natural numbers"))
           (lambda () (top-interp '{substring "hello world" 2.5 11} 20)))

; eval tests
(check-equal? (eval (primopV 'equal? 2 '()) (numV 2) (numV 2)) (boolV #t))
(check-equal? (eval (primopV 'equal? 2 '()) (numV 2) (numV 10)) (boolV #f))
(check-equal? (eval (primopV 'equal? 2 '()) (boolV #f) (boolV #f)) (boolV #t))
(check-equal? (eval (primopV 'equal? 2 '()) (strV "a") (strV "a")) (boolV #t))
(check-equal? (eval (primopV 'equal? 2 '()) (strV "a") (strV "b")) (boolV #f))

; serialize tests
(check-equal? (serialize (interp (parse '{{blam {x} {<= x 0}} 10}) top-env (make-initial-store 25))) "false")
(check-equal? (serialize (interp (parse '{{blam {x} {<= x 0}} 0}) top-env (make-initial-store 25))) "true")
(check-equal? (serialize (primopV '+ 2 '())) "#<primop>")
(check-equal? (serialize (nullV)) "null")
(check-equal? (serialize (arrayV 2 5)) "#<array>")
(check-equal? (serialize (closV (list 'x 'y) (numC 10) '())) "#<procedure>")

; top-interp tests
(check-exn (regexp (regexp-quote "put: (PAIG) Out of memory"))
           (lambda () (top-interp '{{blam {x} {do {aset! x 2 100} {/ {/ {aref x 2} 5} {aref x 1}}}}
               {make-array 5 2}} 20)))
(check-exn (regexp (regexp-quote "initial-store: (PAIG) Not enough memory for initial bindings"))
           (lambda () (top-interp '{substring "hello world" 6 11} 10)))
(check-equal?
 (top-interp '{{blam {x y} {do {x := 10} {y := 5} {* x y}}} 5 2} 22) "50")
(check-exn (regexp (regexp-quote "interp: (PAIG) invalid function: (numC 3)"))
           (lambda () (top-interp '{3 4 5} 20)))

(check-exn (regexp (regexp-quote
                    "type-check: (PAIG) Given return type and body return type do not match"))
           (lambda () (type-check
                       (parse '(rec ((blam ((c : num)) "abc") as a returning num) : 13)) base-tenv)))

[(recC func fp fpT fname retT b)
     (match func
       [(blamC p pT body)
        (match (equal? (type-check body env) retT)
          [#t (type-check b (append env (tbind (list fname) (list (funT fpT retT)))))]
          [#f (error 'type-check "(PAIG) Given return type and body return type do not match")])])]