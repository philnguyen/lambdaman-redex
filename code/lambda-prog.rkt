#lang racket/base
(require redex/reduction-semantics "lambda-compiler.rkt")

(define-term mine.λ
  (with-constants ([enum: #f #t]
                   [enum: ♯ □ · o % Λ =] ; map content
                   [Pill-Worth 10]
                   [Power-Pill-Worth 50]
                   [Ghost-Worth-Least 200]
                   [enum: Standard Fright-Mode Invisible] ; ghost status
                   [enum: ↑ → ↓ ←]
                   [Λ-Ticks-Per-Step 127]
                   [Fright-Mode-Duration ,(* 127 20)]
                   [Search-Depth 3]
                   [MT (LIST)]
                   [Void 0])
    ; generic functions independent of game
    (defrec (; ℕ ℕ → ℕ
             (def (max x y) (if (CGT x y) x y))
             (def (min x y) (if (CGT x y) y x))
             
             ; (Listof (Any × ℕ)) Any ℕ → Any
             (def (max-arg l default-x default-v)
               (LIST-CASE l
                 [(CONS h r) (LET ([(tuple: x v) h]
                                   [update? (CGT v default-v)])
                               (if update?
                                   (max-arg r x v)
                                   (max-arg r default-x default-v)))]
                 [MT default-x]))
             
             (def (any? p l)
               (LIST-CASE l
                 [(CONS x r) (OR (p x) (any? p r))]
                 [MT #f]))
             
             (def (all? p l)
               (LIST-CASE l
                 [(CONS x r) (AND (p x) (all? p r))]
                 [MT #t]))
             
             (def (map f l)
               (LIST-CASE l
                 [(CONS x r) (CONS (f x) (map f r))]
                 [MT MT]))
             
             ; (Listof Any) → ℕ
             (def (len l)
               (LIST-CASE l [(CONS _ r) (ADD 1 (len r))] [MT 0]))
             
             ; (Tableof Any) → ℕ
             (def (table-size m)
               (LIST-CASE m
                 [(CONS x _) (MUL (len m) (len x))]
                 [MT 0]))

             ; (Listof Any) ℕ Any → Any
             (def (list-ref l i default)
               (LIST-CASE l
                 [(CONS x y) (if (CEQ i 0) x (list-ref y (SUB i 1) default))]
                 [MT default]))
             
             ; (Listof Any) ℕ Any → (Listof Any)
             (def (list-upd l i v)
               (LIST-CASE l
                 [(CONS x r) (if i
                                 (CONS x (list-upd r (SUB i 1) v))
                                 (CONS v r))]
                 [MT MT])) ; supress error...
             
             ; (Tableof Any) ℕ ℕ Any → Any
             (def (table-ref m x y default)
               (list-ref (list-ref m y MT) x default))
             
             ; (Tableof Any) ℕ ℕ Any → (Tableof Any)
             (def (table-upd m x y v)
               (list-upd m y (list-upd (list-ref m y ♯) x v)))
             
             ; Dir → Dir
             (def (¬dir d) (INT-CASE d [↑ ↓] [→ ←] [↓ ↑] #:else →))
             
             ; ℕ → ℕ
             (def (level→fruit-worth l)
               (INT-CASE l
                 [1 100]
                 [2 300]
                 [3 500]
                 [4 500]
                 [5 700]
                 [6 700]
                 [7 1000]
                 [8 1000]
                 [9 2000]
                 [10 2000]
                 [11 3000]
                 [12 3000]
                 #:else 5000))
             )
      ; Fixed values for a single game
      (LET* ([(tuple: m₀ Λ₀ G₀ •) w₀]
             [(tuple: loc₀ dir₀) Λ₀]
             [Height (len m₀)]
             [Width (if Height (len (CAR m₀)) 0)]
             [Area (MUL Height Width)]
             [Level (ADD 1 (DIV Area 100))]
             [Fruit-Worth (level→fruit-worth Level)]
             [EOL (MUL Area ,(* 127 16))])
       (defrec (; ℕ² Dir → ℕ²
                (def (step/loc p d)
                  (LET ([(tuple: x y) p])
                   (INT-CASE d
                    [↑ (TUPLE x (SUB y 1))]
                    [→ (TUPLE (ADD x 1) y)]
                    [↓ (TUPLE x (ADD y 1))]
                    #:else (TUPLE (SUB x 1) y))))
             
                (def (step/ghost maze ghost)
                  (LET* ([(tuple: vitality loc dir) ghost]
                         [loc₁ (step/loc loc dir)]
                         [(tuple: x₁ y₁) loc₁]
                         [bounced? (CEQ ♯ (table-ref maze x₁ y₁ □))])
                    (COND
                     [bounced? (LET ([dir₁ (¬dir dir)])
                                 (TUPLE vitality (step/loc loc dir₁) dir₁))]
                     #:else (TUPLE vitality loc₁ dir))))
             
             ; State ℕ → ℕ
             (def (freedom s depth)
               (INT-CASE depth
                [0 (LET ([(tuple: • man • •) s]
                         [(tuple: • • • lives •) man])
                     lives)] ; TODO
                #:else (LET ([s↑ (step s ↑)]
                             [s→ (step s →)]
                             [s↓ (step s ↓)]
                             [s← (step s ←)]
                             [depth-1 (SUB depth 1)])
                         (ADD* (if (ATOM s↑) 0 (freedom s↑ depth-1))
                               (if (ATOM s→) 0 (freedom s→ depth-1))
                               (if (ATOM s↓) 0 (freedom s↓ depth-1))
                               (if (ATOM s←) 0 (freedom s← depth-1))))))
             
             ; State Dir → (State ∪ #f)
             (def (step s dir)
               (LET* ([(tuple: maze λ-man ghosts fruit) s]
                      [(tuple: vitality loc •dir lives score) λ-man]
                      [(tuple: x y) loc]
                      [loc₁ (step/loc loc dir)]
                      [(tuple: x₁ y₁) loc₁]
                      [c₁ (table-ref maze x₁ y₁ □)])
                 (COND
                  ; Skip state if hit wall
                  [(CEQ c₁ ♯) #f]
                  [(CEQ lives 0) #f]
                  #:else
                  (LET ([maze₁! maze]
                        [ghosts₁ (map (λ (g) (step/ghost maze g)) ghosts)]
                        [vitality₁! (max 0 (SUB vitality Λ-Ticks-Per-Step))]
                        [fruit₁ (max 0 (SUB fruit Λ-Ticks-Per-Step))]
                        [score₁! score])
                    (BEGIN
                     (dbg loc₁)
                     ; Update effect of eating stuff
                     (INT-CASE c₁
                      [· (BEGIN (set! maze₁! (table-upd maze₁! x₁ y₁ □))
                                (set! score₁! (ADD score₁! Pill-Worth)))]
                      [o (BEGIN (set! maze₁! (table-upd maze₁! x₁ y₁ □))
                                (set! score₁! (ADD score₁! Power-Pill-Worth))
                                (set! vitality₁! Fright-Mode-Duration))]
                      [% (BEGIN (set! maze₁! (table-upd maze₁! x₁ y₁ □))
                                (set! score₁! (ADD score₁! Fruit-Worth)))]
                      #:else Void)
                     (COND
                      ; If hit ghost ...
                      [(any? (λ (g) (LET ([(tuple: xᵢ yᵢ) g])
                                      (AND (CEQ x₁ xᵢ) (CEQ y₁ yᵢ))))
                             ghosts₁)
                       (if vitality₁!
                           ; ... fright-mode, eat if!
                           (TUPLE
                            maze₁!
                            (TUPLE vitality₁! loc₁ dir lives (ADD score₁! Ghost-Worth-Least))
                            (map (λ (g) (LET ([(tuple: vitᵢ locᵢ dirᵢ) g])
                                          (TUPLE Fright-Mode locᵢ (¬dir dirᵢ))))
                                 ghosts₁)
                            fruit₁)
                           ; ... usually die though
                           (TUPLE
                             maze₁!
                             (TUPLE 0 loc₀ dir₀ (SUB lives 1) score₁!)
                             G₀
                             fruit₁))]
                      #:else
                      (TUPLE maze₁!
                            (TUPLE vitality₁! loc₁ dir lives score₁!)
                            ghosts₁
                            fruit₁)))))))
             
             ; State Dir → Dir
             (def (choose-dir s default-dir steps-left)
               (LET ([depth (min steps-left Search-Depth)]
                     [s↑ (step s ↑)]
                     [s→ (step s →)]
                     [s↓ (step s ↓)]
                     [s← (step s ←)])
                (LET ([n↑ (if (ATOM s↑) 0 (freedom s↑ depth))]
                      [n→ (if (ATOM s→) 0 (freedom s→ depth))]
                      [n↓ (if (ATOM s↓) 0 (freedom s↓ depth))]
                      [n← (if (ATOM s←) 0 (freedom s← depth))])
                  (max-arg (LIST (TUPLE ↑ n↑) (TUPLE → n→) (TUPLE ↓ n↓) (TUPLE ← n←))
                           default-dir 0)))))
             
         (CONS 0 (λ (aiᵢ wᵢ)
                   (CONS (ADD aiᵢ Λ-Ticks-Per-Step)
                         (choose-dir wᵢ ← (DIV (SUB EOL aiᵢ) Λ-Ticks-Per-Step))))))))))

(parameterize ([free-vars '([w₀ •])])
  (dump/opt (term mine.λ)))
