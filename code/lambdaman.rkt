#lang racket/base
(require racket/match racket/string racket/list redex/reduction-semantics)

(define-language L
  ;; GCC syntax
  [(gcc gcc₀ gcc₁ gcc₂) (LDC $n)
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
                        (cmt string)]
  [GCC (gcc ... dec ...)]
  [(dec dec₀ dec₁ dec₂) (: ℓ gcc ...)]
  [($n $i $t $f) integer ℓ #|FIXME|#]
  [(m n i) integer]
  [(ℓ ℓ₀ ℓ₁ ℓ₂) variable-not-otherwise-mentioned]
  ;; basic language
  [(e e₀ e₁ e₂ eₓ) (λ (x ...) e) (e e ...) (o₁ e) (o₂ e e) (if e e e) x b n]
  [o₁ CAR CDR ATOM]
  [o₂ ADD SUB MUL DIV CEQ CGT CGTE CONS]
  [o o₁ o₂]
  [b boolean]
  [ρ ((x ...) ...)]
  [(x y z) variable-not-otherwise-mentioned]
  ;;
  [symtab (side-condition (name symtab any) (hash? (term symtab)))])

;; syntactic sugar
(define-metafunction L
  LET : ([x e] ...) e -> e
  [(LET ([x e_x] ...) e) ((λ (x ...) e) e_x ...)])

(define fresh-label!
  (let ([suffix -1])
    (λ ()
      (set! suffix (+ 1 suffix))
      (string->symbol (format "ℓ~a" suffix)))))

(define-metafunction L
  T : e -> GCC
  [(T e) (t () e)])

(define-metafunction L
  t : ρ e -> GCC
  [(t _ #t) ([LDC 1])]
  [(t _ #f) ([LDC 0])]
  [(t _ n) ([LDC n])]
  [(t ρ x) ([LD n i]) (where (n i) (index-of ρ x))]
  [(t ρ (o e ...)) (gcc ... o dec ...)
   (where (gcc ... dec ...) (t* ρ e ...))]
  [(t ρ (if e₀ e₁ e₂))
   (gcc₀ ... (SEL ℓ₁ ℓ₂) dec₀ ... dec₁ ... dec₂ ... (: ℓ₁ gcc₁ ... JOIN) (: ℓ₂ gcc₂ ... JOIN))
   (where (gcc₀ ... dec₀ ...) (t ρ e₀))
   (where (gcc₁ ... dec₁ ...) (t ρ e₁))
   (where (gcc₂ ... dec₂ ...) (t ρ e₂))
   (where ℓ₁ ,(fresh-label!))
   (where ℓ₂ ,(fresh-label!))]
  [(t ρ (e eₓ ...)) (gcc_1 ... gcc_i ... [AP n] RTN dec_1 ... dec_i ...)
   (where (gcc_1 ... dec_1 ...) (t ρ e))
   (where (gcc_i ... dec_i ...) (t* ρ eₓ ...))
   (where n ,(length (term (eₓ ...))))]
  [(t (any ...) (λ (x ...) e)) ([LDF ℓ] dec ... (: ℓ gcc ...))
   (where (gcc ... dec ...) (t ((x ...) any ...) e))
   (where ℓ ,(fresh-label!))])

(define-metafunction L
  t* : ρ e ... -> GCC
  [(t* ρ e ...) (gcc ... ... dec ... ...)
   (where ((gcc ... dec ...) ...) ((t ρ e) ...))])

;; convert symbolic program to absolute program
(define-metafunction L
  ↓ : GCC -> (gcc ...)
  [(↓ (gcc ... (: ℓ gcc_i ...) ...))
   ((↓ᵢ symtab gcc_flattened) ...)
   (where (gcc_flattened ...) (gcc ... gcc_i ... ...))
   (where n_0 ,(length (term (gcc ...))))
   (where (n_i ...) ,(map length (term ((gcc_i ...) ...))))
   (where symtab ,(let*-values ([(_ ns)
                                 (for/fold ([n_acc (term n_0)]
                                            [n⋯ (list (term n_0))])
                                           ([li (term (n_i ...))])
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
         [(? list? l) (string-join (for/list ([x l]) (format "~a" x)) " " #:before-first "  ")]
         [x (format "  ~a" x)]))
     "\n"
     #:after-last "\n")])

(define (dump-sym e) (printf (term (fm (T ,e)))))
(define (dump e) (printf (term (fm (↓ (T ,e))))))

;; Example programs
(define-term ex1
  ((λ (x) (ADD x x)) 21))

(define-term ex2
  ((λ (x) (if x 2 3)) 42))

(define-term ex3
  (LET ([x 1] [y 2]) (MUL x y)))
