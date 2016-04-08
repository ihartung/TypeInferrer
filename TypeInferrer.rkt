#lang plai

(define-type Expr
  [num (n number?)]
  [id (v symbol?)]
  [bool (b boolean?)]
  [bin-num-op (op procedure?) (lhs Expr?) (rhs Expr?)]
  [iszero (e Expr?)]
  [bif (test Expr?) (then Expr?) (else Expr?)]
  [with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [rec-with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [fun (arg-id symbol?) (body Expr?)]
  [app (fun-expr Expr?) (arg-expr Expr?)]
  [tempty]
  [tcons (first Expr?) (rest Expr?)]
  [tfirst (e Expr?)]
  [trest (e Expr?)]
  [istempty (e Expr?)])
 
(define-type Type
  [t-num]
  [t-bool]
  [t-list (elem Type?)]
  [t-fun (arg Type?) (result Type?)]
  [t-var (v symbol?)])
 
(define-type Constraint
  [eqc (lhs Type?) (rhs Type?)])



;op-table
; : (listof (list/c symbol? (number? number? . -> . number?)))
(define op-table
  (list
   (list '+ +)
   (list '- -)
   (list '* *)))
   
  
;(lookup-op op) → (or/c procedure? false/c)
;  op : symbol?
(define (look-up op)
  (if (boolean? (assoc op op-table))
      #f
      (second (assoc op op-table))))


;(parse se) → Expr?
(define (parse se)
  (cond
    [(number? se) (num se)]
    [(equal? se 'true) (bool #t)]
    [(equal? se 'false) (bool #f)]
    [(symbol? se) (if(or (equal? se '+)
                           (equal? se '*)
                           (equal? se '-)
                           (equal? se 'with)
                           (equal? se 'fun)
                           (equal? se 'bif)
                           (equal? se 'nempty)
                           (equal? se 'iszero))
                    (error 'parse (string-append "not an id: " (symbol->string se)))
                    (id se))]
    [(and (list? se) (not (empty? se)))
     (cond
       [(and (procedure? (look-up (first se))) (not (= (length (rest se)) 2))) (error 'parse "Illegal syntax")]
       [(and (not (number? (first se))) (> (length (rest se)) 1))
        (case (first se)
          [(+) (bin-num-op (look-up '+)
                           (parse (second se))
                           (parse (third se)))]
          [(-) (bin-num-op (look-up '-)
                           (parse (second se))
                           (parse (third se)))]
          [(*) (bin-num-op (look-up '*)
                           (parse (second se))
                           (parse (third se)))]
          [(with) (with (first (second se)) (parse (second (second se))) (parse (third se)))]
          [(rec) (rec-with (first (second se)) (parse (second (second se))) (parse (third se)))]
          [(fun) (fun (first (second se)) (parse (third se)))]
          [(bif) (bif (parse (second se))
                          (parse (third se))
                          (parse (fourth se)))]
          [(tcons) (tcons (parse (second se)) (parse (append '(tcons) (rest (rest se)))))]
          [else (error 'parse "Illegal syntax")]
          
          )]
       [(and (symbol? (first se)) (= (length (rest se)) 1))
        (cond
          [(equal? (first se) 'iszero) (iszero (parse (second se)))]
          [(equal? (first se) 'istempty) (istempty (parse (second se)))]
          [(equal? (first se) 'tfirst) (tfirst (parse (second se)))]
          [(equal? (first se) 'trest) (trest (parse (second se)))]
          [(equal? (first se) 'tcons) (tcons (parse (second se)) (tempty))]
          [else (error 'parse "Illegal syntax")]
          )]
       [(and (list? (first se)) (equal? 'fun (first (first se))))
                    (app (parse (first se))
                         (parse (second se)))]
       )]
    
[(and (list? se) (empty? se)) (tempty)]
[else (error 'parse "Illegal syntax")]))


(define av_hash (make-hash))

;(alpha-vary e) → Expr?
;  e : Expr?
(define (alpha-vary e) (begin0
                         (av e)
                         (hash-clear! av_hash)))



(define (av e)
  (type-case Expr e
    [num (n) e]
    [id (v) (id (hash-ref av_hash v (lambda () (error 'alpha-vary (string-append "unbound ID: " (symbol->string v))))))]
    [bool (b) e]
    [bin-num-op (o l r) (bin-num-op o (av l) (av r))]
    [iszero (e) (iszero (av e))]
    [bif (test then else) (bif (av test) (av then) (av else))]
    [with (bound-id bound-body body)
          (local
            [(define bb (av bound-body))]
            (begin
              (hash-set! av_hash bound-id (gensym bound-id))
              ;(write (hash-ref av_hash 'x))
              (with (hash-ref av_hash bound-id) bb (av body))
              ))]
    [rec-with (bound-id bound-body body)
            (begin
              (hash-set! av_hash bound-id (gensym bound-id))
              (rec-with (hash-ref av_hash bound-id) (av bound-body) (av body)))]
    [fun (arg-id body)
         (begin
              (hash-set! av_hash arg-id (gensym arg-id))
              (fun (hash-ref av_hash arg-id) (av body)))]
    [app (fun-expr arg-expr) (app (av fun-expr) (av arg-expr))]
    [tempty () e]
    [tcons (first rest) e]
    [tfirst (x) e]
    [trest (x) e]
    [istempty (x) e]))


;(generate-constraints e-id e) → (listof Constraint?)
;  e-id : symbol?
;  e : Expr?

;(unify loc) → (listof Constraint?)
;  loc : (listof Constraint?)
(define (unify loc)
  (cond
    [(empty? loc) empty]
    [(cons? loc)
     (let ([l (eqc (first loc))]
           [r (eqc (first loc))])
       (type-case Type l
         [t-num () loc]
         [t-bool () loc]
         [t-list (et) loc]
         [t-fun (at rt) loc]
         [t-var (st) loc]
         ))]))
       

;(infer-type e) → Type?
;  e : Expr?
(define (infer-type e) e)




; type=?/mapping : hash hash Type Type -> Bool
; determines if types are equal modulo renaming
(define (type=?/mapping ht1 ht2 t1 t2)
  (define (teq? t1 t2)
    (type=?/mapping ht1 ht2 t1 t2))
  (cond
    [(and (t-num? t1) (t-num? t2)) true]
    [(and (t-bool? t1) (t-bool? t2)) true]
    [(and (t-list? t1) (t-list? t2))
     (teq? (t-list-elem t1) (t-list-elem t2))]
    [(and (t-fun? t1) (t-fun? t2))
     (and (teq? (t-fun-arg t1) (t-fun-arg t2))
          (teq? (t-fun-result t1) (t-fun-result t2)))]
    [(and (t-var? t1) (t-var? t2))
     (local ([define v1 ; the symbol that ht1 says that t1 maps to
               (hash-ref
                ht1 (t-var-v t1)
                (lambda ()
                  ; if t1 doesn't map to anything, it's the first
                  ; time we're seeing it, so map it to t2
                  (hash-set! ht1 (t-var-v t1) (t-var-v t2))
                  (t-var-v t2)))]
             [define v2
               (hash-ref
                ht2 (t-var-v t2)
                (lambda ()
                  (hash-set! ht2 (t-var-v t2) (t-var-v t1))
                  (t-var-v t1)))])
       ; we have to check both mappings, so that distinct variables
       ; are kept distinct. i.e. a -> b should not be isomorphic to
       ; c -> c under the one-way mapping a => c, b => c.
       (and (symbol=? (t-var-v t2) v1)
            (symbol=? (t-var-v t1) v2)))]
    [(and (Type? t1) (Type? t2)) false]
    [else (error 'type=? "either ~a or ~a is not a Type" t1 t2)]))
 
; type=? Type -> Type -> Bool
; signals an error if arguments are not variants of Type
(define ((type=? t1) t2)
  (or (type=?/mapping (make-hash) (make-hash) t1 t2)
      ; Unfortunately, test/pred simply prints false;
      ; this helps us see what t2 was.
      (error 'type=?
             "~s and ~a are not equal (modulo renaming)"
             t1 t2)))
 
(test/pred (t-var 'a)
           (type=? (t-var 'b)))
(test/pred (t-fun (t-var 'a) (t-var 'b))
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'b))
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'a)) ; fails
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'b)) ; fails
           (type=? (t-fun (t-var 'c) (t-var 'c))))
(test/exn ((type=? 34) 34) "not a Type")
 
; constraint-list=? : Constraint list -> Constraint list -> Bool
; signals an error if arguments are not variants of Constraint
(define ((constraint-list=? lc1) lc2)
  (define htlc1 (make-hash))
  (define htlc2 (make-hash))
  (or (andmap (lambda (c1 c2)
                (and
                 (type=?/mapping
                  htlc1 htlc2
                  (eqc-lhs c1) (eqc-lhs c2))
                 (type=?/mapping
                  htlc1 htlc2
                  (eqc-rhs c1) (eqc-rhs c2))))
              lc1 lc2)
      (error 'constraint-list=?
             "~s and ~a are not equal (modulo renaming)"
             lc1 lc2)))



;__________________________________________________TESTS___________________________________________________________

;Function: alpha-vary
; * Is there an example of alpha-varying a number expression properly?
(test (alpha-vary (parse 5)) (num 5))
; * Is there an example of alpha-varying a true expression properly?
(test (alpha-vary (parse 'true)) (bool #t))
; * Is there an example of alpha-varying a false expression properly?
(test (alpha-vary (parse 'false)) (bool #f))
; * Is there an example of alpha-varying a + expression properly?
(test (alpha-vary (parse '(+ 4 5))) (parse '(+ 4 5)))
; * Is there an example of alpha-varying a - expression properly?
(test (alpha-vary (parse '(- 4 5))) (parse '(- 4 5)))
; * Is there an example of alpha-varying a * expression properly?
(test (alpha-vary (parse '(* 4 5))) (parse '(* 4 5)))
; * Is there an example of alpha-varying a iszero expression properly?
(test (alpha-vary (parse '(iszero 0))) (parse '(iszero 0)))
; * Is there an example of alpha-varying a bif expression properly?
(test (alpha-vary (parse '(bif true 4 5))) (parse '(bif true 4 5)))
; * Is there an example of alpha-varying a id expression properly?
(test/exn (alpha-vary (parse 'x)) "unbound")
; * Is there an example of alpha-varying a with expression properly?
;(test (alpha-vary (parse '(with (x 5) x))) ...)
; * Is there an example of alpha-varying a rec expression properly?
;(test (alpha-vary (parse '(rec (x (+ x 4)) x))) ...)
; * Is there an example of alpha-varying a fun expression properly?
(test (alpha-vary (parse '(fun (x) x))) (parse '(fun (x) x)))
; * Is there an example of alpha-varying a app expression properly?
(test (alpha-vary (parse '((fun (x) x) 5))) (parse '((fun (x) x) 5)))
; * Is there an example of alpha-varying a tempty expression properly?
(test (alpha-vary (parse '())) (tempty))
; * Is there an example of alpha-varying a tcons expression properly?
(test (alpha-vary (parse '(tcons 4 5))) (parse '(tcons 4 5)))
; * Is there an example of alpha-varying a tempty? expression properly?
(test (alpha-vary (parse '(istempty ()))) (parse '(istempty ())))
; * Is there an example of alpha-varying a tfirst expression properly?
(test (alpha-vary (parse '(tfirst (tcons 4 5)))) (parse '(tfirst (tcons 4 5))))
; * Is there an example of alpha-varying a trest expression properly?
(test (alpha-vary (parse '(trest (tcons 4 5)))) (parse '(trest (tcons 4 5))))

;Function: generate-constraints
; * Is the function correct?
; * Is the function documented correctly (i.e. contract and purpose statement)?
; * Is there an example of generating constraints for a number expression?
; * Is there an example of generating constraints for a true expression?
; * Is there an example of generating constraints for a false expression?
; * Is there an example of generating constraints for a + expression?
; * Is there an example of generating constraints for a - expression?
; * Is there an example of generating constraints for a * expression?
; * Is there an example of generating constraints for a iszero expression?
; * Is there an example of generating constraints for a bif expression?
; * Is there an example of generating constraints for a id expression?
; * Is there an example of generating constraints for a with expression?
; * Is there an example of generating constraints for a rec expression?
; * Is there an example of generating constraints for a fun expression?
; * Is there an example of generating constraints for a app expression?
; * Is there an example of generating constraints for a tempty expression?
; * Is there an example of generating constraints for a tcons expression?
; * Is there an example of generating constraints for a tempty? expression?
; * Is there an example of generating constraints for a tfirst expression?
; * Is there an example of generating constraints for a trest expression?

;Function: unify
; * Is the function correct?
; * Is the function documented correctly (i.e. contract and purpose statement)?
; * Is there a Case 1 case test?
; * Is there a Case 2 case test?
; * Is there a Case 2 (occurs check) case test?
; * Is there a Case 3 case test?
; * Is there a Case 4 (lists) case test?
; * Is there a Case 4 (functions) case test?
; * Is there a Case 5 case test?

;Function: infer-type
; * Is the function correct?
; * Is the function documented correctly (i.e. contract and purpose statement)?
; * Does infer-type allow through runtime errors?

; Expression:  num
; * Is there an example of infer-type on a correct num expression?

; Expression:  true
; * Is there an example of infer-type on a correct true expression?

; Expression:  false
; * Is there an example of infer-type on a correct false expression?

; Expression:  +
; * Is there an example of infer-type on a correct + expression?
; * Is there a test case for a lhs error?
; * Is there a test case for a rhs error?

; Expression:  -
; * Is there an example of infer-type on a correct - expression?
; * Is there a test case for a lhs error (not a number)?
; * Is there a test case for a rhs error (not a number)?

; Expression:  *
; * Is there an example of infer-type on a correct * expression?
; * Is there a test case for a lhs error (not a number)?
; * Is there a test case for a rhs error (not a number)?

; Expression:  iszero
; * Is there an example of infer-type on a correct iszero expression?
; * Is there a test case for an input that is not a number?

; Expression:  bif
; * Is there an example of infer-type on a correct bif expression?
; * Is there a test case for a non-boolean conditional error?
; * Is there a test case for a branch return value mismatch error?

; Expression:  id
; * Is there an example of infer-type on a correct id expression?
; * Is there a test case for an unbound identifier?

; Expression:  with
; * Is there an example of infer-type on a correct with expression?
; * Is there a test case for a mis-use of a bound variable?

; Expression:  rec
; * Is there an example of infer-type on a correct rec expression?
; * Is there a test case for a mis-use of a bound variable in bexpr?
; * Is there a test case for a mis-use of a bound variable in body?

; Expression:  fun
; * Is there an example of infer-type on a correct fun expression?
; * Is there a test case for a mis-use of the formal parameter?

; Expression:  app
; * Is there an example of infer-type on a correct app expression?
; * Is there a test case for the operator not a function?
; * Is there a test case for a wrong argument?

; Expression:  tempty
; * Is there an example of infer-type on a correct tempty expression?

; Expression:  tcons
; * Is there an example of infer-type on a correct tcons expression?
; * Is there a test case for an element mismatch?
; * Is there a test case for not a list?

; Expression:  tempty?
; * Is there an example of infer-type on a correct tempty? expression?
; * Is there a test case for not a list?

; Expression:  tfirst
; * Is there an example of infer-type on a correct tfirst expression?
; * Is there a test case for not a list?

; Expression:  trest
; * Is there an example of infer-type on a correct trest expression?
; * Is there a test case for not a list?

;Extra Credit:
; * Is there a test case for A -> B from infer-type?