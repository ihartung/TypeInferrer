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
          [(fun) (fun (first (second se)) (parse (third se)))]
          [(bif) (bif (parse (second se))
                          (parse (third se))
                          (parse (fourth se)))]
          [else (if (= (length se) 2)
                    (app (parse (first se))
                         (parse (second se)))
                    (error 'parse "Illegal syntax"))]
          
          )]
       [(and (symbol? (first se)) (= (length (rest se)) 1))
        (cond
          [(equal? (first se) 'iszero) (iszero (parse (second se)))]
          [(equal? (first se) 'istempty) (istempty (parse (second se)))]
          [(equal? (first se) 'tfirst) (tfirst (parse (second se)))]
          [(equal? (first se) 'trest) (trest (parse (second se)))]
          [else (error 'parse "Illegal syntax")])]
       [else
        (if (> (length se) 1)
            (tcons (parse (first se)) (parse (rest se)))
            (tcons (parse (first se)) (tempty)))]
       )]
[(and (list? se) (empty? se)) (tempty)]
[else (error 'parse "Illegal syntax")]))


(define av_hash (make-hash))

;(alpha-vary e) → Expr?
;  e : Expr?
(define (alpha-vary e)
  (type-case Expr e
    [num (n) e]
    [id (v) (id (hash-ref av_hash v))]
    [bool (b) e]
    [bin-num-op (o l r) e]
    [iszero (e) e]
    [bif (test then else) e]
    [with (bound-id bound-body body)
            (begin
              (hash-set! av_hash bound-id (gensym bound-id))
              (with (hash-ref av_hash bound-id) (alpha-vary bound-body) (alpha-vary body)))]
    [rec-with (bound-id bound-body body) e]
    [fun (arg-id body) e]
    [app (fun-expr arg-expr) e]
    [tempty () e]
    [tcons (first rest) e]
    [tfirst (e) e]
    [trest (e) e]
    [istempty (e) e]))


;(generate-constraints e-id e) → (listof Constraint?)
;  e-id : symbol?
;  e : Expr?

;(unify loc) → (listof Constraint?)
;  loc : (listof Constraint?)

;(infer-type e) → Type?
;  e : Expr?




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