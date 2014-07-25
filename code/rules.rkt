#lang typed/racket/base
(require racket/match racket/set racket/function)

(define-type Element (U " " "#" "." "o" "%" "\\" "="))

(define-type World Any)

(: tick : World → World)
(define tick (compose apply-7 apply-6 apply-5 apply-4 apply-3 apply-2 apply-1))

