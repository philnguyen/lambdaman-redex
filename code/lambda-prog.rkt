#lang racket/base
(require redex/reduction-semantics "lambdaman.rkt")

(define-term mine.λ
  (with-constants ([enum: #f #t]
                   [enum: Wall Empty Pill Power-Pill Fruit Λ-Man-Start Ghost-Start]
                   [enum: Standard Fright-Mode Invisible]
                   [enum: ↑ → ↓ ←]
                   [Search-Depth 10])
    (defrec ((def (list-ref l i default)
               (LIST-CASE l
                 [(CONS x y) (if (CEQ i 0) x (list-ref y (SUB i 1)))]
                 [MT default]))
             
             (def (table-ref m x y)
               (list-ref (list-ref m y Wall) x Wall))
             
             ; (Option State) Dir → (Option State)
             (def (step s dir)
               #f)
             
             ; State ℕ → ℕ
             (def (freedom s depth)
               (COND
                [(CEQ depth 0) 1] ; TODO
                #:else (LET ([s↑ (step s ↑)]
                             [s→ (step s →)]
                             [s↓ (step s ↓)]
                             [s← (step s ←)]
                             [depth-1 (SUB depth 1)])
                         (LET ([n↑ (if (ATOM s↑) 0 (freedom s↑ depth-1))]
                               [n→ (if (ATOM s→) 0 (freedom s→ depth-1))]
                               [n↓ (if (ATOM s↓) 0 (freedom s↓ depth-1))]
                               [n← (if (ATOM s←) 0 (freedom s← depth-1))])
                           (ADD* n↑ n→ n↓ n←)))))
             
             ; ℕ ℕ → ℕ
             (def (max x y) (if (CGT x y) x y))
             
             ; (Listof (Any × ℕ)) Any ℕ → Any
             (def (max-arg l default-x default-v)
               (LIST-CASE l
                 [(CONS h r) (WITH-TUPLE h (x v)
                               (LET ([update? (CGT v default-v)])
                                 (if update?
                                     (max-arg r x v)
                                     (max-arg r default-x default-v))))]
                 [MT default-x]))
             
             ; State Dir → State
             (def (choose-dir s default-dir)
               (LET ([s↑ (step s ↑)]
                     [s→ (step s →)]
                     [s↓ (step s ↓)]
                     [s← (step s ←)])
                (LET ([n↑ (if (ATOM s↑) 0 (freedom s↑ Search-Depth))]
                      [n→ (if (ATOM s→) 0 (freedom s→ Search-Depth))]
                      [n↓ (if (ATOM s↓) 0 (freedom s↓ Search-Depth))]
                      [n← (if (ATOM s←) 0 (freedom s← Search-Depth))])
                  (max-arg (LIST (TUPLE ↑ n↑) (TUPLE → n→) (TUPLE ↓ n↓) (TUPLE ← n←))
                           default-dir 0)))))
    (CONS
     42
     (λ (aiᵢ wᵢ)
       (CONS
        42
        (choose-dir wᵢ ←))
       #;(WITH-TUPLE wᵢ (map man • •)
         (WITH-TUPLE man (• man-loc man-dir • •)
           (WITH-TUPLE man-loc (x y)
             (CONS
              aiᵢ
              (LET ([DOWN (table-ref map x (ADD y 1))]
                    [UP (table-ref map x (SUB y 1))]
                    [RIGHT (table-ref map (ADD x 1) y)]
                    [LEFT (table-ref map (SUB x 1) y)])
                (COND
                 [(CEQ DOWN Power-Pill) ↓]
                 [(CEQ UP Power-Pill) ↑]
                 [(CEQ RIGHT Power-Pill) →]
                 [(CEQ LEFT Power-Pill) ←]
                 [(CEQ DOWN Pill) ↓]
                 [(CEQ UP Pill) ↑]
                 [(CEQ RIGHT Pill) →]
                 [(CEQ LEFT Pill) ←]
                 [(CGT DOWN Wall) ↓]
                 [(CGT UP Wall) ↑]
                 [(CGT RIGHT Wall) →]
                 [(CGT LEFT Wall) ←]
                 #:else man-dir)))))))))))

(dump/opt (term mine.λ))
