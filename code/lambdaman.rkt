#lang racket/base
(require racket/match racket/string racket/list redex/reduction-semantics)

(define-language L
  ;; GCC syntax
  [(gcc gcc₀ gcc₁ gcc₂ gccₓ) (LDC $n)
                             (LD $n $i)
                             ADD SUB MUL DIV
                             CEQ CGT CGTE
                             ATOM
                             CONS CAR CDR
                             (SEL $t $f)
                             JOIN
                             (LDF $f)
                             (AP $n)
                             RTN
                             (DUM $n)
                             (RAP $n)
                             STOP
                             ; Tail call extensions
                             (TSEL $t $f)
                             (TAP $n)
                             (TRAP $n)
                             ; Pascal extensions
                             (ST $n $i)
                             ; Debug extensions
                             DBUG BRK
                             ; target language comment
                             (cmt any)]
  [GCC (gcc ... dec ...)]
  [(dec dec₀ dec₁ dec₂ decₓ) (: ℓ gcc ...)]
  [($n $i $t $f) integer ℓ #|FIXME|#]
  [(m n i) integer]
  [(ℓ ℓ₀ ℓ₁ ℓ₂ ℓₓ) variable-not-otherwise-mentioned]
  ;; basic language
  [(e e₀ e₁ e₂ eₓ) (λ (x ...) e) (e e ...) (o₁ e) (o₂ e e) (if e e e)
                   (defrec ((def (f x ...) e) ...) e)
                   (set! x e)
                   x n C]
  [o₁ CAR CDR ATOM]
  [o₂ ADD SUB MUL DIV CEQ CGT CGTE CONS]
  [o o₁ o₂]
  [C b
     standard fright-mode invisible
     up right down left
     Wall Empty Pill Power-Pill Fruit-Location Lambda-Man-Starting-Position Ghost-Starting-Position]
  [b boolean]
  [(ρ ρₓ) ((x ...) ...)]
  [(f x x₀ x₁ x₂ y z) variable-not-otherwise-mentioned]
  ;;
  [symtab (side-condition (name symtab any) (hash? (term symtab)))])

;; Macros
(define-metafunction L
  LET : ([x e] ...) e -> e
  [(LET ([x e_x] ...) e) ((λ (x ...) e) e_x ...)])
(define-metafunction L
  LET* : ([x e] ...) e -> e
  [(LET* () e) e]
  [(LET* ([x eₓ] any ...) e) (LET ([x eₓ]) (LET* (any ...) e))])
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
  NTH : e n -> e
  [(NTH e 0) (CAR e)]
  [(NTH e n) (NTH (CDR e) ,(- (term n) 1))])
(define-metafunction L
  LIST : e ... -> e
  [(LIST) 0]
  [(LIST e₁ e ...) (CONS e₁ (LIST e ...))])
(define-metafunction L
  TUPLE : e e ... -> e
  [(TUPLE e) e]
  [(TUPLE e₁ e ...) (CONS e₁ (TUPLE e ...))])
(define-metafunction L
  WITH-TUPLE : x (x x ...) ... e -> e
  [(WITH-TUPLE _ (•) e) e]
  [(WITH-TUPLE x (y) e) (LET ([y x]) e)]
  [(WITH-TUPLE x (• y ...) e)
   (LET ([x₁ (CDR x)])
     (WITH-TUPLE x₁ (y ...) e))
   (where x₁ ,(variable-not-in (term (e y ...)) (term x)))]
  [(WITH-TUPLE x (z y ...) e)
   (LET ([z (CAR x)]
         [x₁ (CDR x)])
     (WITH-TUPLE x₁ (y ...) e))
   (where x₁ ,(variable-not-in (term (e z y ...)) (term x)))])
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
  BEGIN : e e ... -> e
  [(BEGIN e) e]
  [(BEGIN eₓ ... e) (LET ([x eₓ] ...) e)
   (where (x ...) ,(variables-not-in (term e) (make-list (length (term (eₓ ...))) '♥)))])

(define fresh-label!
  (let ([suffix -1])
    (λ ()
      (set! suffix (+ 1 suffix))
      (string->symbol (format "lab~a" suffix)))))
(define (fresh-labels! n)
  (for/list ([_ (in-range 0 n)]) (fresh-label!)))

;; Translate closed λ-program into GCC program
(define-metafunction L
  T : e -> (dec ...)
  [(T e) ((: main gcc ... RTN) dec ...) (where (gcc ... dec ...) (t () e))])

;; Translate open λ-program with given context to GCC program
(define-metafunction L
  t : ρ e -> GCC
  [(t _ C) ([LDC ,(case (term C)
                    [(#f standard up Wall) 0]
                    [(#t fright-mode right Empty) 1]
                    [(invisible down Pill) 2]
                    [(left Power-Pill) 3]
                    [(Fruit-Location) 4]
                    [(Lambda-Man-Starting-Position) 5]
                    [(Ghost-Starting-Position) 6])])]
  [(t _ n) ([LDC n])]
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
   (where n ,(length (term (eₓ ...))))]
  [(t (any ...) (λ (x ...) e)) ([LDF ℓ] (: ℓ gcc ... RTN) dec ...)
   (where ℓ ,(fresh-label!))
   (where (gcc ... dec ...) (t ((x ...) any ...) e))]
  [(t (any ...) (defrec ((def (f x ...) eₓ) ...) e))
   ([DUM n] gccₓ ... ... [LDF ℓ] [RAP n]
    (: ℓ gcc ... RTN) decₓ ... ... dec ...)
   (where ρ ((f ...) any ...))
   (where n ,(length (term (f ...))))
   (where ℓ ,(fresh-label!))
   (where ((gccₓ ... decₓ ...) ...) ((t ρ (λ (x ...) eₓ)) ...))
   (where (gcc ... dec ...) (t ρ e))]
  [(t ρ (set! x e)) (gcc ... [ST n i] [LDC 0] dec ...) ; (set! _) returns 0, to make things compose
   (where (gcc ... dec ...) (t ρ e))
   (where (n i) (index-of ρ x))])

;; TC-optimization afterwards. I don't know how to have it by construction
(define-metafunction L
  opt : (dec ...) -> (dec ...)
  [(opt (any_1 ... (: ℓ gcc ... [AP $n] RTN) any_2 ...))
   (opt (any_1 ... (: ℓ gcc ... [TAP $n]) any_2 ...))
   (side-condition (not (redex-match? L (_ ... (_ ... [AP _] RTN) _ ...) (term (any_1 ...)))))]
  [(opt (any_1 ... (: ℓ gcc ... [RAP $n] RTN) any_2 ...))
   (opt (any_1 ... (: ℓ gcc ... [TRAP $n]) any_2 ...))
   (side-condition (not (redex-match? L (_ ... (_ ... [RAP _] RTN) _ ...) (term (any_1 ...)))))]
  [(opt (any_1 ... (: ℓ gcc ... [SEL ℓ₁ ℓ₂] RTN) any_2 ...))
   (opt (any_5 ... (: ℓ₂ gcc₂ ... RTN) any_6 ...))
   (where (any_3 ... (: ℓ₁ gcc₁ ... JOIN) any_4 ...)
          (any_1 ... (: ℓ gcc ... [TSEL ℓ₁ ℓ₂]) any_2 ...))
   (where (any_5 ... (: ℓ₂ gcc₂ ... JOIN) any_6 ...)
          (any_3 ... (: ℓ₁ gcc₁ ... RTN) any_4 ...))
   (side-condition (not (redex-match? L (_ ... (_ ... [SEL _ _] RTN) _ ...) (term (any_1 ...)))))]
  [(opt any) any])

;; convert symbolic program to absolute program
(define-metafunction L
  ↓ : (dec ...) -> (gcc ...)
  [(↓ ((: ℓ gcc ...) ...))
   ((↓ᵢ symtab gcc_flattened) ...)
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
  ↓ᵢ : symtab gcc -> gcc
  [(↓ᵢ symtab (cmt ℓ)) (cmt ,(format "~a @ ~a" (term ℓ) (hash-ref (term symtab) (term ℓ))))]
  [(↓ᵢ _ (name gcc (cmt _))) gcc]
  [(↓ᵢ symtab (any $n ...)) (any (symtab@ symtab $n) ...)]
  [(↓ᵢ _ gcc) gcc])

(define-metafunction L
  index-of : ρ x -> (n i)
  [(index-of ((y ...) ... (z ... x _ ...) _ ...) x)
   (,(length (term ((y ...) ...))) ,(length (term (z ...))))
   (side-condition (not (member (term x) (term (y ... ...)))))]
  [(index-of ρ x) ,(error (format "variable ~a not found in context ~a" (term x) (term ρ)))])

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
(define (dump e) (printf (term (fm (↓ (T ,e))))))
(define (dump/opt e) (printf (term (fm (↓ (opt (T ,e)))))))

;; Example programs
(define-term local.λ
  ((λ (x) (ADD x x)) 21))

(define-term goto.λ
  (defrec ((def (go n) (to (ADD n 1)))
           (def (to n) (go (SUB n 1))))
    (go 1)))

(define-term fact5.λ
  (defrec ((def (fact n)
             (if n (MUL n (fact (SUB n 1))) 1)))
    (fact 5)))

(define-term fact5.tail.λ
  (defrec ((def (fact n a)
             (if n (fact (SUB n 1) (MUL a n)) a)))
    (fact 5 1)))

(define-term fib5.λ
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

(define-term mine.λ
  (defrec ((def (list-ref l i default)
             (LIST-CASE l
               [(CONS x y) (if (CEQ i 0) x (list-ref y (SUB i 1)))]
               [MT default]))
           (def (table-ref m x y)
             (list-ref (list-ref m y Wall) x Wall)))
    (CONS
     #f
     (λ (aiᵢ wᵢ)
       (WITH-TUPLE wᵢ (map man • •)
         (WITH-TUPLE man (• man-loc man-dir • •)
           (WITH-TUPLE man-loc (x y)
             (CONS
              #f
              (LET ([DOWN (table-ref map x (ADD y 1))]
                    [UP (table-ref map x (SUB y 1))]
                    [RIGHT (table-ref map (ADD x 1) y)]
                    [LEFT (table-ref map (SUB x 1) y)])
                (COND
                 [(CEQ DOWN Power-Pill) down]
                 [(CEQ UP Power-Pill) up]
                 [(CEQ RIGHT Power-Pill) right]
                 [(CEQ LEFT Power-Pill) left]
                 [(CEQ DOWN Pill) down]
                 [(CEQ UP Pill) up]
                 [(CEQ RIGHT Pill) right]
                 [(CEQ LEFT Pill) left]
                 [(CGT DOWN Wall) down]
                 [(CGT UP Wall) up]
                 [(CGT RIGHT Wall) right]
                 [(CGT LEFT Wall) left]
                 #:else man-dir))))))))))

(define-term ex1.λ
  ((λ (x) (if x down left)) 42))

(define-term ex2.λ
  (LET ([x 1] [y 2]) (MUL x y)))
