#lang racket/base
(require racket/match racket/string redex/reduction-semantics)

(define-language L
  ;; GCC syntax
  [gcc (LDC $n)
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
       DBUG BRK]
  [GCC (gcc ... dec ...)]
  [dec (: ℓ gcc ...)]
  [($n $i $t $f) integer ℓ #|FIXME|#]
  [(m n i) integer]
  [(ℓ ℓ₁ ℓ₂) variable-not-otherwise-mentioned]
  ;; basic language
  [(e e₁ e₂ eₓ) (λ (x ...) e) (e e ...) (o₁ e) (o₂ e e) (if e e e) x b n]
  [o₁ CAR CDR ATOM]
  [o₂ ADD SUB MUL DIV CEQ CGT CGTE CONS]
  [o o₁ o₂]
  [b boolean]
  [ρ ((x ...) ...)]
  [(x y z) variable-not-otherwise-mentioned])

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
  [(t ρ (if e ...)) (error "TODO")
   (where (gcc ... dec ...) (t* ρ e ...))]
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

(define-metafunction L
  index-of : ρ x -> (n i)
  [(index-of ((y ...) ... (z ... x _ ...) _ ...) x)
   (,(length (term ((y ...) ...))) ,(length (term (z ...))))
   (side-condition (not (member (term x) (term (y ... ...)))))])

(define-metafunction L
  fm : GCC -> string
  [(fm (gcc ... (: ℓ gcc_ℓ ...) ...))
   ,(string-join
     (for/list ([i (append (term (gcc ...)) (apply append (term (((: ℓ) gcc_ℓ ...) ...))))])
       (match i
         [`(: ,ℓ) (format "~a:" ℓ)]
         [(? list? l) (string-join (for/list ([x l]) (format "~a" x)) " " #:before-first "  ")]
         [x (format "  ~a" x)]))
     "\n")])

;; Example programs
(define-term ex1
  ((λ (x) (ADD x x)) 21))

