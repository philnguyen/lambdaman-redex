#lang racket/base
(provide (all-defined-out))
(require racket/match racket/string racket/list racket/set redex/reduction-semantics)

(define-language L
  ;; GCC syntax
  [(gcc gcc₀ gcc₁ gcc₂ gccₓ) (LDC $n)
                             (LD $n $i)
                             ADD SUB MUL DIV
                             CEQ CGT CGTE
                             ATOM
                             CONS CAR CDR
                             (SEL $t $f) JOIN
                             (LDF $f) (AP $n) RTN
                             (DUM $n) (RAP $n)
                             STOP
                             ; Tail call extensions
                             (TSEL $t $f) (TAP $n) (TRAP $n)
                             ; Pascal extensions
                             (ST $n $i)
                             ; Debug extensions
                             DBUG BRK
                             ; target language comment
                             (cmt any)]
  [GCC (gcc ... dec ...)]
  [gcc* (side-condition (name gcc* (gcc ...)) (<= (length (term gcc*)) 1048576))]
  [(dec dec₀ dec₁ dec₂ decₓ) (: ℓ gcc ...)]
  [($n $i $t $f) integer ℓ #|FIXME|#]
  [(m n i) integer]
  [(ℓ ℓ₀ ℓ₁ ℓ₂ ℓₓ) variable-not-otherwise-mentioned]
  ;; basic language
  [(e e₀ e₁ e₂ eₓ) (λ (x ...) e) (e e ...) (o₁ e) (o₂ e e) (if e e e)
                   (defrec ((def (f x ...) e) ...) e)
                   (set! x! e)
                   (with-constants (C ...) e)
                   (dbg e)
                   X n]
  [C (X n) (enum: X ...)]
  [(X Y Z) x b]
  [b boolean]
  [o₁ CAR CDR ATOM]
  [o₂ ADD SUB MUL DIV CEQ CGT CGTE CONS]
  [o o₁ o₂]
  [(ρ ρₓ) ((x ...) ...)]
  [(f x x₀ x₁ x₂ y y₀ y₁ y₂ z) variable-not-otherwise-mentioned]
  [•x (side-condition (name •x x) (regexp-match? #rx"•.*" (symbol->string (term •x))))]
  [x! (side-condition
       (name x! x)
       (match (symbol->string (term x!))
         [(regexp #rx".*!") #t]
         [_ (begin0 #f
              (printf "Mutable variable ~a must be suffixed with !~n" (term x!)))]))]
  [B (x e) ((tuple: x ...) x)] ; let-binding clause
  ;;
  [symtab (side-condition (name symtab any) (hash? (term symtab)))])

;; Macros
(define-metafunction L
  ADD* : e ... -> e
  [(ADD*) 0]
  [(ADD* e) e]
  [(ADD* e₁ e₂ e ...) (ADD* (ADD e₁ e₂) e ...)])
(define-metafunction L
  LET : (B ...) e -> e
  [(LET ([x e_x] ...) e) ((λ (x ...) e) e_x ...)
   (where _ ; Warn about dead code
          ,(let* ([fv (term (FV e))]
                  [deads (for/list ([x (term (x ...))]
                                    #:unless (or (set-member? fv x) (redex-match? L •x x)))
                           x)])
             (unless (empty? deads)
               (printf "Warning: dead bindings: ~a~n" #;(term e) deads))))]
  [(LET ([x e_x] ... [(tuple: y ...) z] any ...) e)
   (LET ([x e_x] ...) (WITH-TUPLE z (y ...) (LET (any ...) e)))])
(define-metafunction L
  LET* : (B ...) e -> e
  [(LET* () e) e]
  [(LET* (any_1 any ...) e) (LET (any_1) (LET* (any ...) e))])
;; Non-standard + must be int
(define-metafunction L
  AND : e ... -> e
  [(AND) #t]
  [(AND e) e]
  [(AND e₁ e ...) (if e₁ (AND e ...) #f)])
(define-metafunction L
  OR : e ... -> e
  [(OR) #f]
  [(OR e) e]
  [(OR e₁ e ...) (if e₁ #t (OR e ...))])
(define-metafunction L
  LIST : e ... -> e
  [(LIST) 0]
  [(LIST e₁ e ...) (CONS e₁ (LIST e ...))])
(define-metafunction L
  TUPLE : e e ... -> e
  [(TUPLE e) e]
  [(TUPLE e₁ e ...) (CONS e₁ (TUPLE e ...))])
(define-metafunction L
  WITH-TUPLE : x (x x ...) e -> e
  [(WITH-TUPLE _ (•x) e) e]
  [(WITH-TUPLE x (y) e) (LET ([y x]) e)]
  [(WITH-TUPLE x (•x y ...) e)
   (LET ([x₁ (CDR x)]) (WITH-TUPLE x₁ (y ...) e))
   (where x₁ ,(variable-not-in (term (e y ...)) '♥))]
  [(WITH-TUPLE x (z y ...) e)
   (LET ([z (CAR x)]
         [x₁ (CDR x)])
     (WITH-TUPLE x₁ (y ...) e))
   (where x₁ ,(variable-not-in (term (e z y ...)) '♥))])
(define-metafunction L
  LIST-CASE : x [(CONS x y) e] [MT e] -> e
  [(LIST-CASE x [(CONS y z) e₁] [MT e₂])
   (if (ATOM x) e₂
       (LET ([y (CAR x)]
             [z (CDR x)])
         e₁))])
(define-metafunction L
  INT-CASE : x [e e] ... #:else e -> e
  [(INT-CASE _ #:else e) e]
  [(INT-CASE x [eₓ e] any ...) (if (CEQ x eₓ) e (INT-CASE x any ...))])
(define-metafunction L
  COND : [e e] ... #:else e -> e
  [(COND #:else e) e]
  [(COND [e₁ e₂] any ...) (if e₁ e₂ (COND any ...))])
(define-metafunction L
  WHEN : e e -> e
  [(WHEN e e₁) (if e e₁ 0)])
(define-metafunction L
  UNLESS : e e -> e
  [(UNLESS e e₁) (if e 0 e₁)])
(define-metafunction L
  BEGIN : e e ... -> e
  [(BEGIN e) e]
  [(BEGIN eₓ ... e) (LET ([x eₓ] ...) e)
   (where (x ...) ,(variables-not-in (term e) (make-list (length (term (eₓ ...))) '♣)))])
(define-metafunction L
  enumerate : X ... -> ([X n] ...)
  [(enumerate X ...) ,(for/list ([X (term (X ...))] [i (in-naturals)]) `(,X ,i))])


(define fresh-label!
  (let ([suffix -1])
    (λ ()
      (set! suffix (+ 1 suffix))
      (string->symbol (format "lab~a" suffix)))))
(define (fresh-labels! n)
  (for/list ([_ (in-range 0 n)]) (fresh-label!)))

(define free-vars (make-parameter '()))
;; Translate closed λ-program into GCC program
(define-metafunction L
  T : e -> (dec ...)
  [(T e) ((: main gcc ... RTN) dec ...) (where (gcc ... dec ...) (t ,(free-vars) e))])

;; Translate open λ-program with given context to GCC program
(define consts (make-parameter (hash)))
(define arities (make-parameter (hash)))
(define-metafunction L
  t : ρ e -> GCC
  ; Source-level optimization
  [(t ρ (if (CEQ e 0) e₁ e₂)) (t ρ (if e e₂ e₁))]
  [(t ρ (if (CEQ 0 e) e₁ e₂)) (t ρ (if e e₂ e₁))]
  ; Regular rules
  [(t _ n) ([LDC n])]
  [(t _ X) ([LDC n])
   (where n ,(hash-ref (consts) (term X) #f))]
  [(t ρ x) ([LD n i]) (where (n i) (index-of ρ x))]
  [(t ρ (o e ...)) (gcc ... ... o dec ... ...)
   (where ((gcc ... dec ...) ...) ((t ρ e) ...))]
  [(t ρ (if e₀ e₁ e₂))
   (gcc₀ ... (SEL ℓ₁ ℓ₂) (: ℓ₁ gcc₁ ... JOIN) (: ℓ₂ gcc₂ ... JOIN) dec₀ ... dec₁ ... dec₂ ...)
   (where ℓ₁ ,(fresh-label!))
   (where ℓ₂ ,(fresh-label!))
   (where (gcc₀ ... dec₀ ...) (t ρ e₀))
   (where (gcc₁ ... dec₁ ...) (t ρ e₁))
   (where (gcc₂ ... dec₂ ...) (t ρ e₂))]
  [(t ρ (e eₓ ...)) (gccₓ ... ... gcc ... [AP n] dec ... decₓ ... ...)
   (where (gcc ... dec ...) (t ρ e))
   (where ((gccₓ ... decₓ ...) ...) ((t ρ eₓ) ...))
   (where n ,(length (term (eₓ ...))))
   (side-condition
    (match (hash-ref (arities) (term e) #f)
      [#f #t]
      [n (unless (equal? n (length (term (eₓ ...))))
           (error (format "Function ~a expects ~a arguments, given ~a: ~a"
                          (term e) n (length (term (eₓ ...))) (term (eₓ ...)))))]))]
  [(t (any ...) (λ (x ...) e)) ([LDF ℓ] (: ℓ gcc ... RTN) dec ...)
   (side-condition (or (for/first ([x (term (x ...))] #:when (hash-has-key? (consts) x))
                         (error (format "Variable ~a shadows a constant" x)))
                       #t))
   (where ℓ ,(fresh-label!))
   (where (gcc ... dec ...) (t ((x ...) any ...) e))]
  [(t (any ...) (defrec ((def (f x ...) eₓ) ...) e))
   ([DUM n] gccₓ ... ... [LDF ℓ] [RAP n]
    (: ℓ gcc ... RTN) decₓ ... ... dec ...)
   (where any_arities
          ,(for/fold ([m (arities)]) ([f (term (f ...))]
                                      [n (map length (term ((x ...) ...)))])
             (hash-set m f n)))
   (where ρ ((f ...) any ...))
   (where n ,(length (term (f ...))))
   (where ℓ ,(fresh-label!))
   (where ((gccₓ ... decₓ ...) ...)
          ,(for/list ([e (term ((λ (x ...) eₓ) ...))])
             (parameterize ([arities (term any_arities)])
               (term (t ρ ,e)))))
   (where (gcc ... dec ...)
          ,(parameterize ([arities (term any_arities)])
             (term (t ρ e))))
   (where _ ; Warn about dead code
          ,(let ([fv (apply set-union (term ((FV e) (FV eₓ) ...)))]) ; TODO may miss some
             (for ([f (term (f ...))])
               (unless (or (set-member? fv f) (redex-match? L •x f))
                 (printf "Warning: function ~a is unused~n" f)))))]
  [(t ρ (set! x e)) (gcc ... [ST n i] [LDC 0] dec ...) ; (set! _) returns 0, to make things compose
   (where (gcc ... dec ...) (t ρ e))
   (where (n i) (index-of ρ x))]
  [(t ρ (with-constants ([X n] ... (enum: Y ...) any ...) e))
   (t ρ (with-constants ([X n] ... [Y m] ... any ...) e))
   (where ([Y m] ...) (enumerate Y ...))]
  [(t ρ (with-constants ([X n] ...) e))
   ,(parameterize ([consts (for/fold ([m (consts)]) ([X (term (X ...))] [n (term (n ...))])
                             (hash-set m X n))])
      (term (t ρ e)))]
  [(t ρ (dbg e)) (gcc ... DBUG [LDC 0] dec ...)
   (where (gcc ... dec ...) (t ρ e))])

;; TC-optimization afterwards. I don't know how to have it by construction
;; FIXME: This function is the bottle neck
(define-metafunction L
  opt : (dec ...) -> (dec ...)
  [(opt (any_1 ... (: ℓ gcc ... [SEL ℓ₁ ℓ₂] RTN) any_2 ...))
   (opt (any_5 ... (: ℓ₂ gcc₂ ... RTN) any_6 ...))
   (where (any_3 ... (: ℓ₁ gcc₁ ... JOIN) any_4 ...)
          (any_1 ... (: ℓ gcc ... [TSEL ℓ₁ ℓ₂]) any_2 ...))
   (where (any_5 ... (: ℓ₂ gcc₂ ... JOIN) any_6 ...)
          (any_3 ... (: ℓ₁ gcc₁ ... RTN) any_4 ...))
   (side-condition (not (redex-match? L (_ ... (_ ... [SEL _ _] RTN) _ ...) (term (any_1 ...)))))]
  [(opt (any_1 ... (: ℓ gcc ... [AP $n] RTN) any_2 ...))
   (opt (any_1 ... (: ℓ gcc ... [TAP $n]) any_2 ...))
   (side-condition (not (redex-match? L (_ ... (_ ... [AP _] RTN) _ ...) (term (any_1 ...)))))]
  [(opt (any_1 ... (: ℓ gcc ... [RAP $n] RTN) any_2 ...))
   (opt (any_1 ... (: ℓ gcc ... [TRAP $n]) any_2 ...))
   (side-condition (not (redex-match? L (_ ... (_ ... [RAP _] RTN) _ ...) (term (any_1 ...)))))]
  [(opt any) any])

;; convert symbolic program to absolute program
(define-metafunction L
  || : (dec ...) -> gcc*
  [(|| ((: ℓ gcc ...) ...))
   ((||ᵢ symtab gcc_flattened) ...)
   (where ((gcc_ann ...) ...) (([cmt ℓ] gcc ...) ...))
   (where (gcc_flattened ...) (gcc_ann ... ...))
   (where (n ...) ,(map length (term ((gcc ...) ...))))
   (where symtab ,(let*-values ([(_ ns)
                                 (for/fold ([n_acc 0] [n⋯ (list 0)]) ([li (term (n ...))])
                                   (let ([ni (+ n_acc li)])
                                     (values ni (cons ni n⋯))))])
                    (for/hash ([ℓ (term (ℓ ...))] [i (reverse (rest ns))])
                      (values ℓ i))))])

;; convert command to use absolute address
(define-metafunction L
  symtab@ : symtab $n -> n
  [(symtab@ _ n) n]
  [(symtab@ symtab ℓ) ,(hash-ref (term symtab) (term ℓ))])
(define-metafunction L
  ||ᵢ : symtab gcc -> gcc
  [(||ᵢ symtab (cmt ℓ)) (cmt ,(format "~a @ ~a" (term ℓ) (hash-ref (term symtab) (term ℓ))))]
  [(||ᵢ _ (name gcc (cmt _))) gcc]
  [(||ᵢ symtab (any $n ...)) (any (symtab@ symtab $n) ...)]
  [(||ᵢ _ gcc) gcc])

(define-metafunction L
  index-of : ρ x -> (n i)
  [(index-of ((y ...) ... (z ... x _ ...) _ ...) x)
   (,(length (term ((y ...) ...))) ,(length (term (z ...))))
   (side-condition (not (member (term x) (term (y ... ...)))))]
  [(index-of ρ x) ,(error (format "Variable ~a not found in context ~a" (term x) (term ρ)))])

(define-metafunction L
  FV : e -> any #|Setof x|#
  [(FV (λ (x ...) e)) ,(set-subtract (term (FV e)) (list->set (term (x ...))))]
  [(FV (o e ...)) ,(apply set-union (term ((FV e) ...)))]
  [(FV (e₁ e ...)) ,(apply set-union (term ((FV e₁) (FV e) ...)))]
  [(FV (if e ...)) ,(apply set-union (term ((FV e) ...)))]
  [(FV (defrec ((def (f x ...) eₓ) ...) e))
   ,(set-subtract (apply set-union (term ((FV e) (FV (λ (x ...) eₓ)) ...)))
                  (list->set (term (f ...))))]
  [(FV (set! x! e)) ,(set-add (term (FV e)) (term x!))]
  [(FV (with-constants _ e)) (FV e)]
  [(FV (dbg e)) (FV e)]
  [(FV x) ,(set (term x))]
  [(FV _) ,(set)])

(define-metafunction L
  fm : GCC -> string
  [(fm (gcc ... (: ℓ gcc_ℓ ...) ...))
   ,(string-join
     (for/list ([i (append (term (gcc ...)) (apply append (term (((: ℓ) gcc_ℓ ...) ...))))])
       (match i
         [`(: ,ℓ) (format "~a:" ℓ)]
         [`(cmt ,s) (format "; ~a:" s)]
         [(? list? l) (string-join (for/list ([x l]) (format "~a" x)) " " #:before-first "  ")]
         [x (format "  ~a" x)]))
     "\n"
     #:after-last "\n")])

(define (dump-sym e) (printf (term (fm (T ,e)))))
(define (dump-sym/opt e) (printf (term (fm (opt (T ,e))))))
(define (dump e) (printf (term (fm (|| (T ,e))))))
(define (dump/opt e) (printf (term (fm (|| (opt (T ,e)))))))

;; Example programs
(define-term local.λ
  ((λ (x) (ADD x x)) 21))

(define-term goto.λ
  (defrec ((def (go n) (to (ADD n 1)))
           (def (to n) (go (SUB n 1))))
    (go 1)))

(define-term sum.λ
  (defrec ((def (sum n)
             (if n (ADD n (sum (SUB n 1))) 0)))
    (sum 42)))

(define-term fact.tail.λ
  (defrec ((def (fact n a)
             (if n (fact (SUB n 1) (MUL a n)) a)))
    (fact 5 1)))

(define-term ack.λ
  (defrec ((def (ack m n)
             (if m (if n
                       (ack (SUB m 1) (ack m (SUB n 1)))
                       (ack (SUB m 1) 1))
                 (ADD n 1))))
    (ack 4 1)))

(define-term fib.λ
  (defrec ((def (fib n)
             (if (CGT n 2) (ADD (fib (SUB n 1)) (fib (SUB n 2))) n)))
    (fib 5)))

(define-term always-down.λ
  (CONS 42
        (λ (AIᵢ wᵢ) ; step
          (CONS (ADD AIᵢ 1) down))))

(define-term rev.λ
  (defrec ((def (rev l a)
             (LIST-CASE l
               [(CONS x y) (rev y (CONS x a))]
               [MT a])))
    (rev (LIST 1 2 3) 0)))

(define-term rev/foldl.λ
  (defrec ((def (foldl f x l)
             (LIST-CASE l
               [(CONS z zs) (foldl f (f z x) zs)]
               [MT x]))
           (def (rev l)
             (foldl (λ (x y) (CONS x y)) 0 l)))
    (rev (LIST 1 2 3))))



(define-term ex1.λ
  ((λ (x) (if x down left)) 42))

(define-term ex2.λ
  (LET ([x 1] [y 2]) (MUL x y)))
