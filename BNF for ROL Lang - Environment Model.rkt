#lang pl

;;;;;;;;;;;;;;;;;;;Q1;;;;;;;;;;;;;
#| BNF for the ROL language:
	<ROL>  ::=  {reg-len = <num><RegE>}
	<RegE> ::=   <Bits> | {and <RegE><RegE>} | {or <RegE><RegE>} | {shl<RegE>} | {with {<ID><RegE>} <RegE>} | {<ID>} |
                     {if <Bool> <RegE> <RegE>} | {fun {<ID>} <RegE>} | {call <RegE><RegE>} | {xor <RegE><RegE>}
	<Bool> ::=   {false} | {true} | {maj? {<RegE>}} | {geq? {<RegE> <RegE>}}
	<Bits> ::=   0 | 1 | <Bits>...
        
|#  
 
;; Defining two new types 
(define-type BIT = (U 0 1)) 
(define-type Bit-List = (Listof BIT)) 

;; RegE abstract syntax trees   
(define-type RegE     
[Reg  Bit-List]
[And  RegE RegE]     
[Or   RegE RegE]
[Xor RegE RegE]
[Shl  RegE]     
[Id   Symbol]     
[With Symbol RegE RegE]     
[Bool Boolean]     
[Geq RegE RegE]     
[Maj RegE]     
[If RegE RegE RegE]
[Call RegE RegE]
[Fun Symbol RegE])
 
;; Next is a technical function that converts (casts) ;; (any) list into a bit-list. We use it in parse-sexpr.
(: list->bit-list : (Listof Any) -> Bit-List)  ;; to cast a list of bits as a bit-list  
(define (list->bit-list lst)   
	(cond [(null? lst) null]  
		[(eq? (first lst) 1)(cons 1 (list->bit-list (rest lst)))] 
		[else (cons 0 (list->bit-list (rest lst)))])) 
 
(: parse-sexpr : Sexpr -> RegE)  ;; to convert the main s-expression into ROL
(define (parse-sexpr sexpr)  
 	(match sexpr
          [(list 'reg-len '= (number: n) sexp)
              (if (> n 0)
                  (parse-sexpr-RegL sexp n) ;; remember to make sure specified register length is at least 1  
		  (error 'parse-sexpr "Register length must be at least 1 ~s" sexpr))]))
(: parse-sexpr-RegL : Sexpr Number -> RegE)  ;; to convert s-expressions into RegEs
(define (parse-sexpr-RegL sexpr reg-len)
   (match sexpr   
	[(list (and a (or 1 0)) ... )
         (if (= reg-len(length a)) (Reg (list->bit-list a))
             (error 'parse-sexpr "wrong number of bits in ~s" a))]
	[(list 'and l1 l2) (And (parse-sexpr-RegL l1 reg-len) (parse-sexpr-RegL l2 reg-len))]
        [(list 'or l1 l2)  (Or (parse-sexpr-RegL l1 reg-len)  (parse-sexpr-RegL l2 reg-len))]
        [(list 'xor l1 l2) (Xor (parse-sexpr-RegL l1 reg-len) (parse-sexpr-RegL l2 reg-len))]
	[(list 'shl R) (Shl (parse-sexpr-RegL R reg-len))]
        [(list 'geq? a b) (Geq (parse-sexpr-RegL a reg-len)(parse-sexpr-RegL b reg-len))]
        [(list 'maj? a) (Maj (parse-sexpr-RegL a reg-len))]
        [(symbol: id) (match id
        ;;This was treacky one. We cahnged it only when we discovered that the boolean value was read as Id.
                        [(symbol: 'true)  (Bool #t)]
                        [(symbol: 'false) (Bool #f)]
                        [(symbol: id) (Id id)])]
        [(cons 'with args)
         (match sexpr
         [(list 'with (list (symbol: name) named-expr) body)
          (With name (parse-sexpr-RegL named-expr reg-len)(parse-sexpr-RegL body reg-len))]
           [else (error 'parse-sexpr-RegL "bad 'with syntax in ~s" sexpr)])]
        [(list 'if a b c) (If (parse-sexpr-RegL a reg-len)(parse-sexpr-RegL b reg-len)(parse-sexpr-RegL c reg-len))]
        [(list 'call fun arg) (Call (parse-sexpr-RegL fun reg-len) (parse-sexpr-RegL arg reg-len))]
        [(cons 'fun args)
         (match sexpr
           [(list 'fun (list (symbol: name)) body)
           (Fun name (parse-sexpr-RegL body reg-len))]
           [else (error 'parse-sexpr-RegL "bad `fun syntax in ~s" sexpr)])]
	[else (error 'parse-sexpr-RegL "bad syntax in ~s" sexpr)]))
        ;[(boolean: b) (Bool b)] isn't required, since there isn't a way to recieve boolean here.
 
(: parse : String -> RegE)  ;; parses a string containing a RegE expression to a RegE AST  
(define (parse str)
       (parse-sexpr (string->sexpr str)))

;;;;;;;;;;;;;;;;;Q2;;;;;;;;;;;;;;;;;
;It actually took us several minutes to complete q2.
;It was difficult to understand we need another name for boolean, other than the typical Bool.

(define-type RES
  [RegV Bit-List]
  [boo Boolean]
  [FunV Symbol RegE ENV])

;;;;;;;;;;;;;;;;;;;Q4;;;;;;;;;;;;;;;;
;We tried to do something unorthodox in the helper functions, only after it didn't work we changed it back. This question took about 4 hours.

#| Formal specs for `eval':
 eval(Reg) = Reg
 eval(bl) = bl
 eval(true) = true
 eval(false) = false
 eval({and E1 E2}) = (<x1 bit-and y1> <x2 bit-and y2> ... <xk bit-and yk>), where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk)
 eval({or E1 E2}) = (<x1 bit-or y1> <x2 bit-or y2> ... <xk bit-or yk>), where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk)
 eval({xor E1 E2}) = (<x1 bit-xor y1> <x2 bit-xor y2> ... <xk bit-xor yk>), where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk)
 eval({shl E}) = (x2 ... xk x1), where eval(E) = (x1 x2 ... xk)
 eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
 eval({if E1 E2 E3}) = eval(E3) if eval(E1) = false
                     = eval(E2) otherwise
 eval({maj? E}) = true if x1+x2+...+xk >= k/2, and false otherwise, where eval(E) = (x1 x2 ... xk)
 eval({Fun E1 E2}) = FunV E1 E2 and the current enviroment.
 eval({Call E1 E2}) = evaluates E2 with E1-enviroment, than, puts the result in E1 and evaluates it.
 eval({geq? E1 E2}) = true if x_i >= y_i, where eval(E1) = (x1 x2 ... xk) and eval(E2) = (y1 y2 ... yk) and i is the first index s.t. x_i and y_i are not equal (or i =k if all are equal)
 eval({if Econd Edo Eelse}) = eval(Edo) if eval(Econd) = true,
                            = eval(Eelse), otherwise.
|#

(define-type ENV
    [EmptyEnv]
    [Extend Symbol RES ENV])

  (: lookup : Symbol ENV -> RES)
  (define (lookup name env)
    (cases env
      [(EmptyEnv) (error 'lookup "no binding for ~s" name)]
      [(Extend id rege rest-env)
       (if (eq? id name) rege (lookup name rest-env))]))

;; Defining functions for dealing with arithmetic operations
;; on the above types
(: bit-and : BIT BIT -> BIT) ;; Arithmetic and. Logic, not Arithmetic!
(define(bit-and a b)
  (if (eq? a b) a 0)) 
(: bit-or : BIT BIT -> BIT) ;; Aithmetic or. Logic, not Arithmetic!
(define(bit-or a b)
  (if (eq? a b) a 1))


;The new ability, Xor:
(: bit-xor : BIT BIT -> BIT)
(define (bit-xor a b)
  (if (eq? a b) 0 1))



(: reg-arith-op : (BIT BIT -> BIT) RES RES -> RES)
;; Consumes two registers and some binary bit operation 'op',
;; and returns the register obtained by applying op on the
;; i'th bit of both registers for all i.
(define (reg-arith-op op reg1 reg2)
(: bit-arith-op : Bit-List Bit-List -> Bit-List)
;; Consumes two bit-lists and uses the binary bit operation 'op'.
;; It returns the bit-list obtained by applying op on the
;; i'th bit of both registers for all i.
(define (bit-arith-op bl1 bl2)
  ( : bit-arith-helper : Bit-List Bit-List Bit-List -> Bit-List)
  (define (bit-arith-helper l1 l2 lresult)
    (if (null? l1) lresult
                   (bit-arith-helper (rest l1) (rest l2) (append lresult (list (op (first l1) (first l2))) ))))
  (bit-arith-helper bl1 bl2 null))
(RegV (bit-arith-op (RegV->bit-list reg1) (RegV->bit-list reg2))))


(: majority? : Bit-List -> Boolean)
;; Consumes a list of bits and checks whether the
;; number of 1's are at least as the number of 0's.
;; The logic is simple- upon recieveing 1 add 1, upon recieveing 0 decrease 1, check if the last result positive or negative.
(define(majority? bl)
  ( : majority?-helper : Bit-List Number -> Boolean)
  (define (majority?-helper lst c)
    (cond
	[(and (null? lst) (or (> c 0) (= c 0))) true]
	[(null? lst) false]
	[(= (first lst) 1) (majority?-helper (rest lst) (+ c 1))]
	[else (majority?-helper (rest lst) (- c 1))]))
  (majority?-helper bl 0))

(: geq-bitlists? : Bit-List Bit-List -> Boolean)
;; Consumes two bit-lists and compares them. It returns true if the
;; first bit-list is larger or equal to the second.
(define (geq-bitlists? bl1 bl2)
   (cond
	[(null? bl1) true] ;;Both lists equal until the last bit. True.
	[(and (= (first bl1) 1) (= (first bl2) 0)) true] ;;bl1[i]>bl2[i]. True
	[(and (= (first bl1) 0) (= (first bl2) 1)) false] ;;bl1[i]<bl2[i]. False
	[else (geq-bitlists? (rest bl1) (rest bl2))])) ;;bl1[i]==bl2[i]. Reccursion.

(: shift-left : Bit-List -> Bit-List)
;; Shifts left a list of bits (once)
(define(shift-left bl)
  (append (rest bl) (list (first bl)))) ;;put the first bit as last.
(: RegV->bit-list : RES -> Bit-List)
;; extract a bit-list from RES type
  (define (RegV->bit-list res)
  (cases res
      [(RegV a) a]
      [else (error 'RegV->bit-list "bad syntax in ~s" res)]))
( : boo->Boolean : RES -> Boolean)
(define (boo->Boolean value)
  (cases value
    [(boo a) (if (eq? a #t) #t #f)]
    [else (error 'boo->Boolean "This is a bit-list, not boolean! in ~s" value)]))
    
  
(: eval : RegE ENV -> RES)
;; evaluates RegE expressions by reducing them to bit-lists

(define (eval expr env)
  (cases expr
    [(Reg a) (RegV a)] 
    [(And a b) (reg-arith-op bit-and (eval a env) (eval b env))]     
    [(Or a b)  (reg-arith-op bit-or  (eval a env) (eval b env))]
    [(Xor a b) (reg-arith-op bit-xor (eval a env) (eval b env))]
    [(Shl a) (RegV (shift-left (RegV->bit-list (eval a env))))] 
    [(With name named-expr body)
     (eval body (Extend name (eval named-expr env) env))]
    [(Bool b) (boo b)] 
    [(Geq a b) (boo (geq-bitlists? (RegV->bit-list (eval a env)) (RegV->bit-list (eval b env))))] 
    [(Maj a) (boo (majority? (RegV->bit-list (eval a env))))]
    [(Id sym) (lookup sym env)]
    [(If cond trueValue falseValue) (if (boo->Boolean (eval cond env)) (eval trueValue env) (eval falseValue env))]
    [(Call fun-expr arg-expr)
     (let ([fval (eval fun-expr env)])
       (cases fval
         ;the minimal change: "f-env" instead of "env"
         [(FunV bound-id bound-body f-env)
          (eval bound-body
                (Extend bound-id (eval arg-expr env) f-env))]
         [else (error 'eval "`call expects a function, got: ~s" fval)]))]
    [(Fun bound-id bound-body)
     (FunV bound-id bound-body env)]))


(: run : String -> Bit-List)
(define (run str)
  (let ([result (eval (parse str) (EmptyEnv))])
  (cases result
    [(RegV a) a]
    [else (error 'run "bad expression, not a bit-list in ~s" result)])))
  
;;;Tests!!
;We used the tests we wrote for HW3, and added about 11 new tests (most are yours from the pdf)

  (test (run "{ reg-len =  4  {1 0 0 0}}") => '(1 0 0 0)) 
  (test (run "{ reg-len =  4  {xor {1 0 0 0} {1 1 1 1}}}") => '(0 1 1 1))  
  (test (run "{ reg-len = 4  {shl {1 0 0 0}}}") => '(0 0 0 1)) 
  (test (run "{ reg-len = 4   
                  {and {shl {1 0 1 0}}{shl {1 0 1 0}}}}") => '(0 1 0 1)) 
  (test (run "{ reg-len = 4   
                  { or {and {shl {1 0 1 0}}  
                            {shl {1 0 0 1}}} {1 0 1 0}}}") => '(1 0 1 1)) 
  (test (run "{ reg-len = 2   
                  { or {and {shl {1 0}} {1 0}} {1 0}}}") => '(1 0)) 
  (test (run "{ reg-len = 4   
                  {with {x {1 1 1 1}} {shl y}}}") =error> "lookup: no binding for y") 
 
  (test (run "{ reg-len = 4   
                 {or {1 1 1 1} {0 1 1}}}") =error>  
                                        "wrong number of bits in (0 1 1)") 
  (test (run "{ reg-len =  0  {}}") =error>  
                                      "Register length must be at least 1") 
  (test (run "{ reg-len =  4  {xor {0 1 1 1} {1 0 0 0}}}") => '(1 1 1 1))  
  (test (run "{ reg-len =  2  {with 
                                   {x 
                                     {xor {1 0} {1 1} } } 
                                 {call {fun {y} {or x y}} 
                                       {0 1}}}}") => '(0 1))
(test (run "{ reg-len =  3 {with {add3 {fun {x} {or x {1 1 1}}}} 
                {call add3 { 0 0 1}}}}") 
        => '(1 1 1)) 
  (test (run "{ reg-len =  3 {with {add3 {fun {x} {and x {1 0 1}}}} 
                {with {add1 {fun {x} {or x {1 1 1}}}} 
                  {with {x {1 1 0}} 
                    {call add1 {call add3 x}}}}}}") 
        => '(1 1 1)) 
  (test (run "{ reg-len =  4 {with {identity {fun {x} x}} 
                {with {foo {fun {x} {or x {1 0 0 1}}}} 
                  {call {call identity foo} {1 1 1 1}}}}}") 
        => '(1 1 1 1)) 
  (test (run "{ reg-len =  2 {with {x {1 1}} 
                {with {f {fun {y} {if {geq? x y} {0 0} {1 0}} }} 
                  {with {x {1 0}} 
                    {call f {0 1}}}}}}") 
        => '(0 0)) 
(test (run "{ reg-len = 4  
                  {if {maj? {0 0 1 1}} {shl {1 0 1 1}} {1 1 0 1}}}") 
        => '(0 1 1 1)) 
(test (run "{ reg-len = 4  
                  {if false {shl {1 0 1 1}} {1 1 0 1}}}")         => '(1 1 0 1))
(test (run "{ reg-len = 4  
                  {if true {shl {1 0 1 1}} {1 1 0 1}}}")         => '(0 1 1 1))

(test (run "{ reg-len = 2 {and {1 0}{0 0}}}") =>'(0 0))
(test (run "{ reg-len = 2 {and {1 0}{1 1}}}") =>'(1 0))
(test (run "{ reg-len = 2 {and {1 1}{0 1}}}") =>'(0 1))
(test (run "{ reg-len = 2 {and {1 1}{1 1}}}") =>'(1 1))
(test (run "{ reg-len = 1 {or {0}{0}}}") =>'(0))
(test (run "{ reg-len = 1 {or {1}{0}}}") =>'(1))
(test (run "{ reg-len = 1 {or {0}{1}}}") =>'(1))
(test (run "{ reg-len = 1 {or {1}{1}}}") =>'(1))
(test (run "{ reg-len = 4 {1 0 0 0}}") => '(1 0 0 0))
(test (run "{ reg-len = 4 {shl {1 0 0 0}}}") => '(0 0 0 1))
(test (run "{ reg-len = 4 {and {shl {1 0 1 0}}{shl {1 0 1 0}}}}") =>'(0 1 0 1))
(test (run "{ reg-len = 4 { or {and {shl {1 0 1 0}} {shl {1 0 0 1}}} {1 0 1 0}}}") =>'(1 0 1 1));(test (run "{ reg-len = 2 { or {and {shl {1 0}} {1 0}} {1 0}}}") => '(1 0));(test (run "{ reg-len = 4 {with {x {1 1 1 1}} {shl y}}}") =error> "free identifier: y")
(test (run "{ reg-len = 2 { with {x { or {and {shl {1 0}} {1 0}} {1 0}}}
         {shl x}}}") => '(0 1)) (test (run "{ reg-len = 4  {or {1 1 1 1} {0 1 1}}}") =error> "wrong number of bits in (0 1 1)")
(test (run "{ reg-len = 0 {}}") =error> "Register length must be at least 1")
(test (geq-bitlists? '(1 0 1) '(1 1 1)) => #f)
(test (geq-bitlists? '(1 1 1) '(1 1 1)) => #t)
(test (geq-bitlists? '(1 0 1) '(0 1 1)) => #t)
(test (run "{ reg-len = 3 {if {geq? {1 0 1} {1 1 1}} {0 0 1} {1 1 0}}}") => '(1 1 0))
(test (run "{ reg-len = 4 {if {maj? {0 0 1 1}} {shl {1 0 1 1}} {1 1 0 1}}}") => '(0 1 1 1))
(test (run "{ reg-len = 4 {if {maj? {0 0 0 1}} {shl {1 0 1 1}} {1 1 0 1}}}") => '(1 1 0 1))
(test (run "{ reg-len = 4 {if false {shl {1 0 1 1}} {1 1 0 1}}}") => '(1 1 0 1))
(test (run "{ reg-len = 4 {if true {shl {1 0 1 1}} {1 1 0 1}}}") => '(0 1 1 1))
(test (run "{reg-len = 1 {maj? {1}}}") =error> "run: bad expression, not a bit-list in (boo #t)")
(test (run "{reg-len = 1 {x}}") =error> "parse-sexpr-RegL: bad syntax in (x)")
(test (run "{reg-len = 1 {fun x}}") =error> "parse-sexpr-RegL: bad `fun syntax in (fun x)")

(test (run "{reg-len = 1 {with { a {0}}}}") =error> "parse-sexpr-RegL: bad 'with syntax in (with (a (0)))")
(test (boo->Boolean (RegV '(1 0))) =error> "boo->Boolean: This is a bit-list, not boolean! in (RegV (1 0))")
(test (RegV->bit-list (boo #t)) =error> "RegV->bit-list: bad syntax in (boo #t)")

;Writing a tests for full coverage took some time. Espically the "error" messages...

(test (eval (Call (Reg '(0 1 1)) (Reg '(0 0 0))) (EmptyEnv)) =error> "eval: `call expects a function, got: (RegV (0 1 1))")

;;;;;;;;;;;;;Q2;;;;;;;;;;;;
;The main problem we had here, was a mistake of the variables types- we started with RegE ENV for some stupid reason...
;We consulted Dani Gilboa, Avi Shaanani and Leora Schmerler (all in order to find the mistake stated in the previous line
;It took about 4 hours from start to end, include tests.

(: help-lookup : Symbol ENV -> Boolean)
(define (help-lookup sym env)
  (cases env
    [(EmptyEnv) #t]
    [(Extend id rege rest-env)
     (if (eq? sym id) #f (help-lookup sym rest-env))]))

(: containsFreeInstance? : RegE ENV -> Boolean)
(define (containsFreeInstance? reg env)
  (cases reg
    [(Reg a) #f]
    [(And a b) (or (containsFreeInstance? a env) (containsFreeInstance? b env))]
    [(Or a b) (or (containsFreeInstance? a env) (containsFreeInstance? b env))]
    [(Xor a b) (or (containsFreeInstance? a env) (containsFreeInstance? b env))]
    [(Shl a) (containsFreeInstance? a env)]
    [(With name named-expr body) (or (containsFreeInstance? named-expr env) (containsFreeInstance? body (Extend name (boo #f) env)))]
;The (boo #f) is in order to have some value in name, not really matter which value.
    [(Bool b) #f]
    [(Geq a b) (or (containsFreeInstance? a env) (containsFreeInstance? b env))]
    [(Maj a) (containsFreeInstance? a env)]
    [(Id sym) (help-lookup sym env)]
    [(If cond trueValue falseValue) (or (containsFreeInstance? cond env) (containsFreeInstance? trueValue env) (containsFreeInstance? falseValue env))]
    [(Fun bound-id bound-body) (containsFreeInstance? bound-body (Extend bound-id (boo #f) env))]
    [(Call fun-expr arg-expr) (or (containsFreeInstance? fun-expr env) (containsFreeInstance? arg-expr env))]
    ))


(: check-code : String -> Boolean) 
(define (check-code str) 
  (containsFreeInstance? (parse str) (EmptyEnv)))

;Tests!!
(test (check-code "{ reg-len =  1 {if true {xor {1} {0}} {0}}}") => #f) 
(test (check-code "{ reg-len = 4  {with {x {1 1 1 1}} {shl y}}}") => #t) 
(test (check-code "{ reg-len =  1 {if {geq? {0} {1}} {0} {0}}}") => #f)
(test (check-code "{ reg-len =  2 {if {maj? {shl {0 1}}} {0 0} {1 1}}}") => #f)
(test (check-code "{ reg-len =  3 {call {fun {x} {or x {1 0 1}}} {0 0 1}}}") => #f) 
(test (check-code "{ reg-len =  3 {call {fun {y} {xor x {0 0 1}}} {0 0 1}}}") => #t) 
(test (check-code "{ reg-len =  3 {call foo {0 0 1}}}") => #t) 
(test (check-code "{ reg-len =  3 {fun {x} {and x {or {1 0 1} {0 0 0}}}}}") => #f)


