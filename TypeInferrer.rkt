#lang plai

(print-only-errors #t)

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
    [(equal? se 'tempty) (tempty)]
    [(symbol? se) (if(or (equal? se '+)
                         (equal? se '*)
                         (equal? se '-)
                         (equal? se 'with)
                         (equal? se 'fun)
                         (equal? se 'bif)
                         (equal? se 'tempty)
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
          [(tcons) (tcons (parse (second se)) (parse (third se)))]
          [else (error 'parse "Illegal syntax")]
          
          )]
       [(and (symbol? (first se)) (= (length (rest se)) 1))
        (cond
          [(equal? (first se) 'iszero) (iszero (parse (second se)))]
          [(equal? (first se) 'tempty?) (istempty (parse (second se)))]
          [(equal? (first se) 'tfirst) (tfirst (parse (second se)))]
          [(equal? (first se) 'trest) (trest (parse (second se)))]
          [(equal? (first se) 'tcons) (tcons (parse (second se)) (tempty))]
          [else (app (parse (first se)) (parse (second se)))]
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
(define (generate-constraints e-id e)
  (type-case Expr e
    [num (n) (list (eqc (t-var e-id) (t-num)))]
    [id (v) (list (eqc (t-var e-id) (t-var v)))]
    [bool (b) (list (eqc (t-var e-id) (t-bool)))]
    [bin-num-op (op l r)
                (local [(define l-id (gensym))
                        (define r-id (gensym))]
                  (append
                   (list
                    (eqc (t-var e-id) (t-num))
                    (eqc (t-var l-id) (t-num))
                    (eqc (t-var r-id) (t-num)))
                   (generate-constraints l-id l)
                   (generate-constraints r-id r)))]
    [iszero (t)
            (local [(define t-id (gensym))]
              (append
               (list
                (eqc (t-var e-id) (t-bool))
                (eqc (t-var t-id) (t-num)))
               (generate-constraints t-id t)))]
    [bif (test then else)
         (local [(define test-id (gensym))
                 (define then-id (gensym))
                 (define else-id (gensym))]
           (append
            (list
             (eqc (t-var e-id) (t-var then-id))
             (eqc (t-var then-id) (t-var else-id))
             (eqc (t-var test-id) (t-bool)))
            (generate-constraints test-id test)
            (generate-constraints then-id then)
            (generate-constraints else-id else)))]
    [with (b-id b-body body)
          (local [(define b-body-id (gensym))
                  (define body-id (gensym))]
            (append
             (list
              (eqc (t-var e-id) (t-var body-id))
              (eqc (t-var b-id) (t-var b-body-id)))
             (generate-constraints b-body-id b-body)
             (generate-constraints body-id body)))]
    [rec-with (b-id b-body body)
              (local [(define b-body-id (gensym))
                      (define body-id (gensym))]
                (append
                 (list
                  (eqc (t-var e-id) (t-var body-id))
                  (eqc (t-var b-id) (t-var b-body-id)))
                 (generate-constraints b-body-id b-body)
                 (generate-constraints body-id body)))]
    [fun (arg body)
         (local [(define body-id (gensym))]
           (cons
            (eqc (t-var e-id) (t-fun (t-var arg) (t-var body-id)))
            (generate-constraints body-id body)))]
    [app (fun arg)
         (local [(define fun-id (gensym))
                 (define arg-id (gensym))]
           (append
            (list (eqc (t-var fun-id) (t-fun (t-var arg-id) (t-var e-id))))
            (generate-constraints fun-id fun)
            (generate-constraints arg-id arg)))]
    [tempty () (list (eqc (t-var e-id) (t-list (t-var (gensym)))))]
    [tcons (f r)
           (local [(define f-id (gensym))
                   (define r-id (gensym))]
             (append
              (list
               (eqc (t-var e-id) (t-list (t-var f-id)))
               (eqc (t-var r-id) (t-list (t-var f-id))))
              (generate-constraints f-id f)
              (generate-constraints r-id r)))]
    [tfirst (c)
            (local [(define c-id (gensym))]
              (append
               (list (eqc (t-var c-id) (t-list (t-var e-id))))
               (generate-constraints c-id c)))]
    [trest (c)
           (local [(define c-id (gensym))]
             (append
              (list
               (eqc (t-var e-id) (t-var c-id))
               (eqc (t-var c-id) (t-list (t-var (gensym)))))
              (generate-constraints c-id c)))]
    [istempty (c)
              (local [(define c-id (gensym))]
                (append
                 (list
                  (eqc (t-var e-id) (t-bool))
                  (eqc (t-var c-id) (t-list (t-var (gensym)))))
                 (generate-constraints c-id c)))]))

;(unify loc) → (listof Constraint?)
;  loc : (listof Constraint?)
(define (unify loc)
  (unify/s loc empty))

;(unify/s loc sub) → (listof Constraint?)
;  loc : (listof Constraint?)
;  sub : (listof Constraint?)
(define (unify/s loc sub)
  (cond
    [(empty? loc) sub]
    [(cons? loc)
     (let ([l (eqc-lhs (first loc))]
           [r (eqc-rhs (first loc))])
       (cond
         [{or [and (t-bool? l) (t-bool? r)] [and (t-num? l) (t-num? r)]}
          (unify/s (rest loc) sub)]
         [(t-var? l)
          (if (occurs l r)
              (error 'unify "Type Error")
              (unify/s (replace-con l r (rest loc) #t)
                       (cons (eqc l r) (replace-con l r sub #f))))]
         [(t-var? r)
          (if (occurs r l)
              (error 'unify "Type Error")
              (unify/s (replace-con r l (rest loc) #t)
                       (cons (eqc r l) (replace-con r l sub #f))))]
         [(and (t-list? l) (t-list? r))
          (unify/s (cons (eqc (t-list-elem l) (t-list-elem r)) (rest loc))
                   sub)]
         [(and (t-fun? l) (t-fun? r))
          (local [(define l-arg (t-fun-arg l))
                  (define r-arg (t-fun-arg r))
                  (define l-res (t-fun-result l))
                  (define r-res (t-fun-result r))
                  (define lara (eqc l-arg r-arg))
                  (define lrrr (eqc l-res r-res))]
            (unify/s
             (append
              (list lara lrrr)
              (rest loc))
             sub))]
         [else (error 'unify "Type Error")]))]))

(define (occurs l r)
  (type-case Type r
    [t-var (v) (symbol=? (t-var-v l) v)]
    [t-num () #f]
    [t-bool () #f]
    [t-list (e) (occurs l e)]
    [t-fun (f a) (or (occurs l f) (occurs l a))]))

;(replace-con a b loc both) → (listof Constraint?)
;   a : Type?
;   b : Type?
;   loc : (listof Constraint?)
;   both : boolean?
(define (replace-con a b loc both)
  (map
   (lambda (e)
     (eqc (if both (replace a b (eqc-lhs e)) (eqc-lhs e))
          (replace a b (eqc-rhs e))))
   loc))

;(replace a b t) -> Type?
;  a : t-var?
;  b : Type?
;  t : Type?
(define (replace a b t)
  (type-case Type t
    [t-num () t]
    [t-bool () t]
    [t-var (v) (if (symbol=? v (t-var-v a)) b t)]
    [t-list (to) (t-list (replace a b to))]
    [t-fun (arg body) (t-fun (replace a b arg) (replace a b body))]))


; (lookup-type c loc) -> Type?
;   c : symbol?
;   loc : (listof Constraint?)
(define (lookup-type c loc)
  (local [(define bond (assoc
                        c
                        (map
                         (lambda (e)
                           (local [(define l (eqc-lhs e))
                                   (define r (eqc-rhs e))]
                             (list (t-var-v l) r)))
                         loc)))]
    (if (boolean? bond)
        (error 'lookup-type "No type mapping")
        (second bond))))

;(infer-type e) → Type?
;  e : Expr?
(define (infer-type e)
  (local [(define e-id (gensym))]
    (lookup-type
     e-id
     (unify (generate-constraints e-id (alpha-vary e))))))

;(run se) -> Type?
(define (run se)
  (infer-type (parse se)))


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
(test (alpha-vary (parse '(tempty? ()))) (parse '(tempty? ())))
; * Is there an example of alpha-varying a tfirst expression properly?
(test (alpha-vary (parse '(tfirst (tcons 4 5)))) (parse '(tfirst (tcons 4 5))))
; * Is there an example of alpha-varying a trest expression properly?
(test (alpha-vary (parse '(trest (tcons 4 5)))) (parse '(trest (tcons 4 5))))

;Function: generate-constraints
; * Is there an example of generating constraints for a number expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '4)))
       (list (eqc (t-var 'g154769) (t-num)))) #t)
; * Is there an example of generating constraints for a true expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse 'true)))
       (list (eqc (t-var 'g155772) (t-bool)))) #t)
; * Is there an example of generating constraints for a false expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse 'false)))
       (list (eqc (t-var 'g155772) (t-bool)))) #t)
; * Is there an example of generating constraints for a + expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(+ a b))))
       (list
        (eqc (t-var 'g157480) (t-num))
        (eqc (t-var 'g157481) (t-num))
        (eqc (t-var 'g157482) (t-num))
        (eqc (t-var 'g157481) (t-var 'a))
        (eqc (t-var 'g157482) (t-var 'b)))) #t)
; * Is there an example of generating constraints for a - expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(- a b))))
       (list
        (eqc (t-var 'g157480) (t-num))
        (eqc (t-var 'g157481) (t-num))
        (eqc (t-var 'g157482) (t-num))
        (eqc (t-var 'g157481) (t-var 'a))
        (eqc (t-var 'g157482) (t-var 'b)))) #t)
; * Is there an example of generating constraints for a * expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(* a b))))
       (list
        (eqc (t-var 'g157480) (t-num))
        (eqc (t-var 'g157481) (t-num))
        (eqc (t-var 'g157482) (t-num))
        (eqc (t-var 'g157481) (t-var 'a))
        (eqc (t-var 'g157482) (t-var 'b)))) #t)
; * Is there an example of generating constraints for a iszero expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(iszero a))))
       (list
        (eqc (t-var 'g158668) (t-bool))
        (eqc (t-var 'g158669) (t-num))
        (eqc (t-var 'g158669) (t-var 'a)))) #t)
; * Is there an example of generating constraints for a bif expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(bif cond one two))))
       (list
        (eqc (t-var 'g159588) (t-var 'g159590))
        (eqc (t-var 'g159590) (t-var 'g159591))
        (eqc (t-var 'g159589) (t-bool))
        (eqc (t-var 'g159589) (t-var 'cond))
        (eqc (t-var 'g159590) (t-var 'one))
        (eqc (t-var 'g159591) (t-var 'two)))) #t)
; * Is there an example of generating constraints for a id expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse 'a)))
       (list (eqc (t-var 'g160853) (t-var 'a)))) #t)
; * Is there an example of generating constraints for a with expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(with (r 4) r))))
       (list
        (eqc (t-var 'g161994) (t-var 'g161996))
        (eqc (t-var 'r) (t-var 'g161995))
        (eqc (t-var 'g161995) (t-num))
        (eqc (t-var 'g161996) (t-var 'r)))) #t)
; * Is there an example of generating constraints for a rec expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse 'a)))
       (list (eqc (t-var 'g160853) (t-var 'a)))) #t)
; * Is there an example of generating constraints for a fun expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(fun (a) a))))
       (list
        (eqc (t-var 'g162885) (t-fun (t-var 'a) (t-var 'g162886)))
        (eqc (t-var 'g162886) (t-var 'a)))) #t)
; * Is there an example of generating constraints for a app expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(f a))))
       (list
        (eqc (t-var 'g169746) (t-fun (t-var 'g169747) (t-var 'g169745)))
        (eqc (t-var 'g169746) (t-var 'f))
        (eqc (t-var 'g169747) (t-var 'a)))) #t)
; * Is there an example of generating constraints for a tempty expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse 'tempty)))
       (list (eqc (t-var 'g171412) (t-list (t-var 'g171413))))) #t)
; * Is there an example of generating constraints for a tcons expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(tcons 1 tempty))))
       (list
        (eqc (t-var 'g172715) (t-list (t-var 'g172716)))
        (eqc (t-var 'g172717) (t-list (t-var 'g172716)))
        (eqc (t-var 'g172716) (t-num))
        (eqc (t-var 'g172717) (t-list (t-var 'g172718))))) #t)
; * Is there an example of generating constraints for a tempty? expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(tempty? tempty))))
       (list
        (eqc (t-var 'g176529) (t-bool))
        (eqc (t-var 'g176530) (t-list (t-var 'g176531)))
        (eqc (t-var 'g176530) (t-list (t-var 'g176532))))) #t)
; * Is there an example of generating constraints for a tfirst expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(tfirst (tcons 4 tempty)))))
       (list
        (eqc (t-var 'g177882) (t-list (t-var 'g177881)))
        (eqc (t-var 'g177882) (t-list (t-var 'g177883)))
        (eqc (t-var 'g177884) (t-list (t-var 'g177883)))
        (eqc (t-var 'g177883) (t-num))
        (eqc (t-var 'g177884) (t-list (t-var 'g177885))))) #t)
; * Is there an example of generating constraints for a trest expression?
(test ((constraint-list=? (generate-constraints (gensym) (parse '(trest (tcons 4 tempty)))))
       (list
        (eqc (t-var 'g41101) (t-var 'g41102))
        (eqc (t-var 'g41102) (t-list (t-var 'g41103)))
        (eqc (t-var 'g41102) (t-list (t-var 'g41104)))
        (eqc (t-var 'g41105) (t-list (t-var 'g41104)))
        (eqc (t-var 'g41104) (t-num))
        (eqc (t-var 'g41105) (t-list (t-var 'g41106))))) #t)

;Function: unify                                    ???????????????
; * Is there a Case 1 case test?
(test (unify (list (eqc (t-num) (t-num))
                   (eqc (t-bool) (t-bool))))
      empty)
; * Is there a Case 2 case test?
(test (unify (list (eqc (t-var 'a) (t-bool))))
      (list (eqc (t-var 'a) (t-bool))))
; * Is there a Case 2 (occurs check) case test?
(test/exn (unify (list (eqc (t-var 'a) (t-var 'a))))
          "Type Error")
(test/exn (unify (list (eqc (t-var 'a) (t-list (t-var 'a)))))
          "Type Error")
(test/exn (unify (list (eqc (t-var 'a) (t-fun (t-var 'a) (t-var 'b)))))
          "Type Error")
(test/exn (unify (list (eqc (t-var 'a) (t-fun (t-var 'b) (t-var 'a)))))
          "Type Error")
; * Is there a Case 3 case test?
(test (unify (list (eqc (t-list (t-var 'a)) (t-var 'b))))
      (list (eqc (t-var 'b) (t-list (t-var 'a)))))
; Occurs check Case 3
(test/exn (unify (list (eqc (t-var 'a) (t-var 'a))))
          "Type Error")
(test/exn (unify (list (eqc (t-list (t-var 'a)) (t-var 'a))))
          "Type Error")
(test/exn (unify (list (eqc (t-fun (t-var 'a) (t-var 'b)) (t-var 'a))))
          "Type Error")
(test/exn (unify (list (eqc (t-fun (t-var 'b) (t-var 'a)) (t-var 'a))))
          "Type Error")
; * Is there a Case 4 (lists) case test?
(test (unify (list (eqc (t-list (t-var 'a)) (t-list (t-var 'b)))))
      (list (eqc (t-var 'a) (t-var 'b))))
; * Is there a Case 4 (functions) case test?
(test (unify (list (eqc (t-fun (t-var 'a) (t-var 'b)) (t-fun (t-var 'c) (t-var 'd)))))
      (list (eqc (t-var 'b) (t-var 'd))
            (eqc (t-var 'a) (t-var 'c))))
; * Is there a Case 5 case test?
(test/exn (unify (list (eqc (t-num) (t-bool))))
          "Type Error")

;Function: infer-type
; * Does infer-type allow through runtime errors?
(test/pred (infer-type (parse '(tfirst tempty))) (type=? (t-var 'b)))


; Expression:  num
; * Is there an example of infer-type on a correct num expression?
(test/pred (infer-type (parse '5)) (type=? (t-num)))


; Expression:  true
; * Is there an example of infer-type on a correct true expression?
(test/pred (infer-type (parse 'true)) (type=? (t-bool)))

; Expression:  false
; * Is there an example of infer-type on a correct false expression?
(test/pred (infer-type (parse 'false)) (type=? (t-bool)))

; Expression:  +
; * Is there an example of infer-type on a correct + expression?
(test/pred (infer-type (parse '(+ 4 5))) (type=? (t-num)))
; * Is there a test case for a lhs error?
(test/exn (infer-type (parse '(+ false 4))) "Type Error")
; * Is there a test case for a rhs error?
(test/exn (infer-type (parse '(+ 4 true))) "Type Error")

; Expression:  -
; * Is there an example of infer-type on a correct - expression?
(test/pred (infer-type (parse '(- 4 5))) (type=? (t-num)))
; * Is there a test case for a lhs error?
(test/exn (infer-type (parse '(- false 4))) "Type Error")
; * Is there a test case for a rhs error?
(test/exn (infer-type (parse '(- 4 true))) "Type Error")

; Expression:  *
; * Is there an example of infer-type on a correct * expression?
(test/pred (infer-type (parse '(* 4 5))) (type=? (t-num)))
; * Is there a test case for a lhs error?
(test/exn (infer-type (parse '(* false 4))) "Type Error")
; * Is there a test case for a rhs error?
(test/exn (infer-type (parse '(* 4 true))) "Type Error")

; Expression:  iszero
; * Is there an example of infer-type on a correct iszero expression?
(test/pred (infer-type (parse '(iszero 5))) (type=? (t-bool)))
; * Is there a test case for an input that is not a number?
(test/exn (infer-type (parse '(iszero false))) "Type Error")

; Expression:  bif
; * Is there an example of infer-type on a correct bif expression?
(test/pred (infer-type (parse '(bif false 4 5))) (type=? (t-num)))
; * Is there a test case for a non-boolean conditional error?
(test/exn (infer-type (parse '(bif (+ 3 3) 4 5))) "Type Error")
; * Is there a test case for a branch return value mismatch error?
(test/exn (infer-type (parse '(bif false tempty 5))) "Type Error")

; Expression:  id
; * Is there an example of infer-type on a correct id expression?
(test/pred (infer-type (parse 'x)) (type=? (t-var 'b)))
; * Is there a test case for an unbound identifier?
(test/exn (infer-type (parse '(with (x 5) y))) "unbound")

; Expression:  with
; * Is there an example of infer-type on a correct with expression?
(test/pred (infer-type (parse '(with (x 5) x))) (type=? (t-num)))
; * Is there a test case for a mis-use of a bound variable?
(test/exn (infer-type (parse '(with (x false) (+ x x)))) "Type Error")

; Expression:  rec
; * Is there an example of infer-type on a correct rec expression?
(test/pred (infer-type (parse
                        '(rec (f (fun (a) (bif (iszero a) a (f (+ a -1))))) f)))
           (type=? (t-fun (t-num) (t-num))))
; * Is there a test case for a mis-use of a bound variable in bexpr?
(test/exn (infer-type (parse
                        '(rec (f (fun (a) (bif (iszero a) d (f (+ a -1))))) f)))
           "unbound")
; * Is there a test case for a mis-use of a bound variable in body?
(test/exn (infer-type (parse
                        '(rec (f (fun (a) (bif (iszero a) d (f (+ a -1))))) g)))
           "unbound")

; Expression:  fun
; * Is there an example of infer-type on a correct fun expression?
(test/pred (infer-type (parse '(fun (x) (- 15 x)))) (type=? (t-fun (t-num) (t-num))))
; * Is there a test case for a mis-use of the formal parameter?               ?????????
(test/exn (infer-type (parse '(fun (x) (bif x (- 15 x) (- 12 x))))) "Type Error")

; Expression:  app
; * Is there an example of infer-type on a correct app expression?
(test/pred (infer-type (parse '((fun (x) (- 15 x)) 5))) (type=? (t-num)))
; * Is there a test case for the operator not a function?                     ?????????????
(test/exn (infer-type (parse '(with (x (tcons 1 tempty)) (x 4)))) "Type Error")
; * Is there a test case for a wrong argument?
(test/exn (infer-type (parse '((fun (x) (- 15 x)) false))) "Type Error")

; Expression:  tempty
; * Is there an example of infer-type on a correct tempty expression?
(test/pred (infer-type (parse 'tempty)) (type=? (t-list (t-var 'b))))

; Expression:  tcons
; * Is there an example of infer-type on a correct tcons expression?
(test/pred (infer-type (parse '(tcons 4 (tcons 5 (tcons 6 tempty)))))
           (type=? (t-list (t-num))))
; * Is there a test case for an element mismatch?
(test/exn (infer-type (parse '(tcons 4 (tcons false (tcons 6 tempty)))))
          "Type Error")
; * Is there a test case for not a list?                    
(test/exn (infer-type (parse '(tcons 4 5))) "Type Error")

; Expression:  tempty?
; * Is there an example of infer-type on a correct tempty? expression?
(test/pred (infer-type (parse '(tempty? (tcons 4 (tcons 5 (tcons 6 tempty))))))
           (type=? (t-bool)))
; * Is there a test case for not a list?
(test/exn (infer-type (parse '(tempty? false))) "Type Error")

; Expression:  tfirst
; * Is there an example of infer-type on a correct tfirst expression?
(test/pred (infer-type (parse '(tfirst (tcons 4 (tcons 5 (tcons 6 tempty))))))
           (type=? (t-num)))
; * Is there a test case for not a list?
(test/exn (infer-type (parse '(tfirst false))) "Type Error")

; Expression:  trest
; * Is there an example of infer-type on a correct trest expression?
(test/pred (infer-type (parse '(trest (tcons 4 tempty))))
           (type=? (t-list (t-num))))
; * Is there a test case for not a list?
(test/exn (infer-type (parse '(trest true))) "Type Error")

;Extra Credit:
; * Is there a test case for A -> B from infer-type?
