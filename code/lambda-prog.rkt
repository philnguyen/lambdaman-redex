
#lang racket/base
(require redex/reduction-semantics "lambda-compiler.rkt")

;; Specific macros for this program (mentioning its free variables)
(define-metafunction L
  MAX* : e e ... -> e
  [(MAX* e) e]
  [(MAX* e₁ e ...) (max e₁ (MAX* e ...))])
(define-metafunction L
  MIN* : e e ... -> e
  [(MIN* e) e]
  [(MIN* e₁ e ...) (min e₁ (MIN* e ...))])
(define-metafunction L
  MAX-ARG* : (e x) (e x) ... -> e
  [(MAX-ARG* (e _)) e]
  [(MAX-ARG* (e₁ x₁) (e₂ x₂) any ...)
   (if (CGT x₁ x₂)
       (MAX-ARG* (e₁ x₁) any ...)
       (MAX-ARG* (e₂ x₂) any ...))])
(define-metafunction L
  MIN-ARG* : (e x) (e x) ... -> e
  [(MIN-ARG* (e _)) e]
  [(MIN-ARG* (e₁ x₁) (e₂ x₂) any ...)
   (if (CGT x₁ x₂)
       (MIN-ARG* (e₂ x₂) any ...)
       (MIN-ARG* (e₁ x₁) any ...))])

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
                   [Lame-Method-Depth 32]
                   [MT (LIST)]
                   [Void 0])
    ; generic functions independent of game
    (defrec (
             ; ℕ ℕ → ℕ
             (def (max x y) (if (CGT x y) x y))
             #;(def (min x y) (if (CGT x y) y x))
             
             ; (Listof (Any × ℕ)) Any ℕ → Any
             (def (min-arg l default-x default-v)
               (LIST-CASE l
                 [(CONS p r) (LET* ([(tuple: x v) p]
                                    [update? (CGT v default-v)])
                               (if update? (min-arg r x v)
                                   (min-arg r default-x default-v)))]
                 [MT default-x]))
             
             (def (any? p l)
               (LIST-CASE l
                 [(CONS x r) (OR (p x) (any? p r))]
                 [MT #f]))
             
             (def (map f l)
               (LIST-CASE l
                 [(CONS x r) (CONS (f x) (map f r))]
                 [MT MT]))
             
             ; (Listof Any) → ℕ
             (def (len l)
               (if (ATOM l) 0 (ADD 1 (len (CDR l)))))

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
             (def (turn-right d)
               (INT-CASE d [↑ →] [→ ↓] [↓ ←] #:else ↑))
             (def (turn-left d)
               (INT-CASE d [↑ ←] [→ ↑] [↓ →] #:else ↓))
             
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
             
             ; ℕ Any → (Listof Any)
             (def (make-list n v)
               (if n (CONS v (make-list (SUB n 1) v)) MT))
             
             ; ℕ ℕ Any → (Tableof Any)
             (def (make-table rows cols v)
               (make-list rows (make-list cols v)))

             ; ℕ ℕ → Boolean
             (def (loc=? p q)
               (LET ([(tuple: x₁ y₁) p]
                     [(tuple: x₂ y₂) q])
                 (AND (CEQ x₁ x₂) (CEQ y₁ y₂))))
             
             ; State → ℕ
             (def (state-eval s)
               (LET ([(tuple: • man •ghosts •) s]
                     [(tuple: • •loc • lives score) man])
                 (MUL lives score)))
             
             #;(def (state-man-dir s)
               (LET ([(tuple: • man • •) s]
                     [(tuple: • • dir • •) man])
                 dir)))
      ; Fixed values for a single game
      (LET* ([(tuple: m₀ Λ₀ G₀ •) w₀]
             [(tuple: •vit loc₀ dir₀ •lives •score) Λ₀]
             [Height (len m₀)]
             [Width (if Height (len (CAR m₀)) 0)]
             [Area (MUL Height Width)]
             [Level (ADD 1 (DIV Area 100))]
             [Fruit-Worth (level→fruit-worth Level)]
             [EOL (MUL Area ,(* 127 16))]
             #;[Empty-Table (make-table Height Width #f)])
       (defrec
         (
          ; ℕ² Dir → ℕ²
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
                   [bounced? (CEQ ♯ (table-ref maze x₁ y₁ ♯))])
              (COND
               [bounced? (LET ([dir₁ (¬dir dir)])
                           (TUPLE vitality (step/loc loc dir₁) dir₁))]
               #:else (TUPLE vitality loc₁ dir))))
          
          ; Lame method.
          ; No fancy searching. Just go straight while I can,
          ; then turn if hit wall
          (def (step+score s dir n)
            (COND
             [(CEQ n 0) 0]
             [(ATOM s) 0]
             #:else (LET* ([s₁ (step s dir)]
                           [n₁ (SUB n 1)])
                      (ADD (state-eval s)
                           (DIV
                            (if (ATOM s₁)
                                (LET* ([dirₗ (turn-left dir)]
                                       [sₗ (step s dirₗ)])
                                  (if (ATOM sₗ)
                                      (LET* ([dirᵣ (turn-right dir)]
                                             [sᵣ (step s dirᵣ)])
                                        (step+score sᵣ dirᵣ n₁))
                                      (step+score sₗ dirₗ n₁)))
                                (step+score s₁ dir n₁))
                            2)))))
          
          ; State → Dir
          (def (ev1 s)
            (LET* ([n↑ (step+score (step s ↑) ↑ Lame-Method-Depth)]
                   [n→ (step+score (step s →) → Lame-Method-Depth)]
                   [n↓ (step+score (step s ↓) ↓ Lame-Method-Depth)]
                   [n← (step+score (step s ←) ← Lame-Method-Depth)])
              (MAX-ARG* [↑ n↑] [→ n→] [↓ n↓] [← n←])))
             
          ; State Dir → (State ∪ #f)
          (def (step s dir)
            (LET* ([(tuple: maze λ-man ghosts fruit) s]
                   [(tuple: vitality loc •dir lives score) λ-man]
                   [loc₁ (step/loc loc dir)]
                   [(tuple: x₁ y₁) loc₁]
                   [c₁ (table-ref maze x₁ y₁ ♯)])
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
                   [(any? (λ (g) (LET ([(tuple: •vitᵢ locᵢ dirᵢ) g])
                                   (OR (loc=? locᵢ loc₁)
                                       (loc=? (step/loc locᵢ dirᵢ) loc₁))))
                          ghosts₁)
                    (if vitality₁!
                        ; ... fright-mode, eat if!
                        (TUPLE
                         maze₁!
                         (TUPLE vitality₁! loc₁ dir lives (ADD score₁! Ghost-Worth-Least))
                         (map (λ (g) (LET ([(tuple: •vitᵢ locᵢ dirᵢ) g])
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
                         fruit₁))))))))
          
         (CONS
          #f
          (λ (aiᵢ wᵢ)
            (CONS #f (ev1 wᵢ)))))))))

(parameterize ([free-vars '([w₀ •])])
  (dump (term mine.λ))
  #;(dump/opt (term mine.λ)))
