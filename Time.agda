-- {-# OPTIONS --safe #-}
module Time where

open import Map
open import Relation.Binary.PropositionalEquality
open import Data.String using (String)
open import Data.Nat
open import Data.Nat.Base using (_≤_)
open import Data.Bool using (true ; false)
open import Data.Bool.Base using (if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_)
open import Data.List
open import Data.Nat.Properties
open import Language

max : ∀ (m n : ℕ) → ℕ
max m n with (m ≤? n)
... | false Relation.Nullary.because _ = m
... | true Relation.Nullary.because _ = n

taeval : (Γ : (String → ℕ)) → (Aexp {ℕ}) → ℕ
taeval Γ (a +` a₁) = taeval Γ a + taeval Γ a₁ + (Γ "+")
taeval Γ (a -` a₁) = taeval Γ a + taeval Γ a₁ + (Γ "-")
taeval Γ (a *` a₁) = taeval Γ a + taeval Γ a₁ + (Γ "*")
taeval Γ (Avar x) = 1           -- Just look up in memory assuming 1
                                -- clock cycle
taeval Γ (Anum x) = 1           -- Just look up in mem is 1 clock cycle


tbeval : (Γ : (String → ℕ)) → (Bexp {ℕ}) → ℕ
tbeval Γ TRUE = Γ "TRUE"
tbeval Γ FALSE = Γ "FALSE"
tbeval Γ (x1 <` x2) = aeval Γ x1 + aeval Γ x2 + (Γ "<")
tbeval Γ (x1 >` x2) = aeval Γ x1 + aeval Γ x2 + (Γ ">")
tbeval Γ (x1 ≤` x2) = aeval Γ x1 + aeval Γ x2 + (Γ "≤")
tbeval Γ (x1 ≥` x2) = aeval Γ x1 + aeval Γ x2 + (Γ "≥")
tbeval Γ (x1 ≡` x2) = aeval Γ x1 + aeval Γ x2 + (Γ "≡")
tbeval Γ (¬` b) = tbeval Γ b + (Γ "NOT")
tbeval Γ (b &&` b₁) = tbeval Γ b + tbeval Γ b₁ + (Γ "AND")
tbeval Γ (b ||` b₁) = tbeval Γ b + tbeval Γ b₁ + (Γ "OR")


-- Time eval as a function. Γ is the map from labels to execution time
-- for a statement
tceval : (Γ : (String → ℕ)) → Cmd {ℕ} → ℕ
tceval Γ SKIP = 0
tceval Γ (l := r) with l
... | Var x = Γ x + (aeval Γ r)
tceval Γ (c ¿ c₁) = (tceval Γ c) + (tceval Γ c₁)
tceval Γ IF b THEN c ELSE c₁ END = max (tceval Γ c) (tceval Γ c₁)
tceval Γ WHILE b DO c END = 0 -- FIXME: Fix this later
tceval Γ (EXEC x) = 0 -- FIXME: Fix this later

-- Semantics of time from here
data _,_,_=[_]=>_ (Γ : (String → Maybe (ProgTuple {ℕ}))) (st : String → ℕ) :
           ℕ → Cmd {ℕ} → ℕ → Set where
 TSKIP : ∀ (W : ℕ) → Γ , st , W =[ SKIP ]=> (W + 0)

 TASSIGN : ∀ (X : String) → ∀ (n : ℕ) → ∀ (e : Aexp {ℕ})
           → ∀ (W : ℕ) →
           ---------------------------------
           Γ , st ,  W =[ (Var X := e) ]=> (W + (tceval st (Var X := e)))

 TSEQ : ∀ (c1 c2 : Cmd {ℕ})
        → ∀ (W W' W'' : ℕ)
        → Γ , st , W =[ c1 ]=> (W + W')
        → Γ , st , (W + W') =[ c2 ]=> (W + (W' + W'')) →
        --------------------------------------------
        Γ , st ,  W =[ c1 ¿ c2 ]=> (W + (W' + W''))

 -- TIF : ∀ (n1 : ℕ) → (b : Bexp {ℕ}) → (t e : Cmd {ℕ}) → ∀ (W : ℕ) →
 --       -----------------------------------------------------------
 --        Γ , st , W =[ (IF b THEN t ELSE e END) ]=>
 --          (W + (tceval st (IF b THEN t ELSE e END) + (tbeval st b)))

 -- XXX: Hack, st contains both exec time and state!
 TIFT : (n1 : ℕ) → (b : Bexp {ℕ}) →
        (t e : Cmd {ℕ}) → ∀ (W : ℕ)
        → (beval st b ≡ true)
        → Γ , st , W =[ (IF b THEN t ELSE e END) ]=>
          (W + (tceval st t + (tbeval st b)))

 TIFE : (n1 : ℕ) → (b : Bexp {ℕ}) →
        (t e : Cmd {ℕ}) → ∀ (W : ℕ)
        → (beval st b ≡ false)
        → Γ , st , W =[ (IF b THEN t ELSE e END) ]=>
          (W + (tceval st e + (tbeval st b)))

-- The worst case time semantics
-- data _,_=[_]=>_ (Γ : String → Maybe (ProgTuple {ℕ})) :
--                 (String →  ℕ) →
--                 Cmd {ℕ} → (String →  ℕ) →
--                 Set where

--  CLF : (st : (String →  ℕ)) →
--        (b : Bexp {ℕ}) → (c : Cmd {ℕ}) →
--         beval st b ≡ false →
--         -----------------------------------------------------------
--         Γ , st =[ (WHILE b DO c END) ]=> st

--  CLT :  (st st' st'' : (String →  ℕ)) →
--         (b : Bexp {ℕ}) → (c : Cmd {ℕ}) →
--         beval st b ≡ true →
--         Γ , st =[ c ]=> st' →
--         Γ , st' =[ (WHILE b DO c END) ]=> st'' →
--         -----------------------------------------------------------
--         Γ , st =[ (WHILE b DO c END) ]=> st''

 -- XXX: Done.
 -- CEX : ∀ (f : FuncCall {ℕ}) → ∀ (st st' : (String → ℕ))
 --       → Γ , st =[ f ]=>ᶠ st'
 --       -----------------------------------------------------------
 --       → Γ , st =[ EXEC f ]=> st'
        
-- Doing the evaluation of top
-- evalProg : {A : Set} → (p : Top {A}) →
--            (st : String → Maybe (ProgTuple {A})) →
--            (String → Maybe (ProgTuple {A}))
-- evalProg MAIN: c END st = (StoreP st "MAIN" (Arg "void" , Ret "void" , c))
-- evalProg (DEF f < x >⇒< x1 >: c END ¿ p) st =
--               StoreP (evalProg p st) f (x , x1 , c)


-- Soundness theorem for SKIP WCET rule
skip-sound : (Γ : String → Maybe (ProgTuple {ℕ}))
           → (Γᵗ : String → ℕ)  -- map of labels to execution times
           → ∀ (W W' X : ℕ) → (cmd : Γ , Γᵗ , W =[ SKIP ]=> W')
           → (W ≡ X) → (W' ≡ X)
skip-sound Γ Γᵗ W .(W + 0) .W (TSKIP .W) refl rewrite +-comm W 0 = refl

-- Soundness theorem for Assign WCET rule
assign-sound : (Γ : String → Maybe (ProgTuple {ℕ}))
             → (Γᵗ : (String → ℕ))
             → (S : String) → (e : Aexp {ℕ})
             → (W W' X n : ℕ) → (cmd : Γ , Γᵗ , W =[ Var S := e ]=> W')
             → (tceval Γᵗ (Var S := e)) ≡ n
             → (W ≡ X) → (W' ≡ X + n)
assign-sound Γ st S e W .(W + tceval st (Var S := e)) .W
  .(tceval st (Var S := e)) (TASSIGN .S n .e .W) refl refl = refl


-- Deterministic exec
Δ-exec : (Γ : String → Maybe (ProgTuple {ℕ}))
         → (Γᵗ : String → ℕ)
         → ∀ (W W' W'' : ℕ) → (c1 : Cmd {ℕ})
         → (Γ , Γᵗ , W =[ c1 ]=> W')
         → (Γ , Γᵗ , W =[ c1 ]=> W'')
         → W' ≡ W''
Δ-exec Γ Γᵗ W .(W + 0) .(W + 0) .SKIP (TSKIP .W) (TSKIP .W) = refl
Δ-exec Γ Γᵗ W .(W + tceval Γᵗ (Var X := e)) .(W + tceval Γᵗ (Var X := e))
 .(Var X := e) (TASSIGN X n e .W) (TASSIGN .X n₁ .e .W) = refl
Δ-exec Γ Γᵗ W .(W + (W' + W''')) .(W + (W'' + W''''))
 .(c1 ¿ c2) (TSEQ c1 c2 .W W' W''' p1 p3) (TSEQ .c1 .c2 .W W'' W'''' p2 p4)
 with Δ-exec Γ Γᵗ W (W + W') (W + W'') c1 p1 p2
... | r with +-cancelˡ-≡ W r
... | refl
 with Δ-exec Γ Γᵗ (W + W') (W + (W' + W''')) (W + (W' + W'''')) c2 p3 p4
... | rr with +-cancelˡ-≡ W rr
... | rm with +-cancelˡ-≡ W' rm
... | refl = refl
Δ-exec Γ Γᵗ W .(W + (tceval Γᵗ t + tbeval Γᵗ b)) .(W + (tceval Γᵗ t + tbeval Γᵗ b)) IF b THEN t ELSE e END (TIFT n2 .b .t .e .W x) (TIFT n1 .b .t .e .W x₁) = refl
Δ-exec Γ Γᵗ W .(W + (tceval Γᵗ e + tbeval Γᵗ b)) .(W + (tceval Γᵗ t + tbeval Γᵗ b)) IF b THEN t ELSE e END (TIFE n2 .b .t .e .W x) (TIFT n1 .b .t .e .W x₁)
  = ⊥-elim (contradiction-lemma b Γᵗ x₁ x)
Δ-exec Γ Γᵗ W .(W + (tceval Γᵗ t + tbeval Γᵗ b)) .(W + (tceval Γᵗ e + tbeval Γᵗ b)) IF b THEN t ELSE e END (TIFT n2 .b .t .e .W x) (TIFE n1 .b .t .e .W x₁)
  = ⊥-elim (contradiction-lemma b Γᵗ x x₁)
Δ-exec Γ Γᵗ W .(W + (tceval Γᵗ e + tbeval Γᵗ b)) .(W + (tceval Γᵗ e + tbeval Γᵗ b)) IF b THEN t ELSE e END (TIFE n2 .b .t .e .W x) (TIFE n1 .b .t .e .W x₁) = refl


skip-exec-time : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (Γ , Γᵗ , W1 =[ SKIP ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ SKIP ]=> (W2 + X2))
               → X1 ≡ X2
skip-exec-time Γ Γᵗ W1 W2 X1 X2 p1 p2 with (W1 + X1) in eq1
skip-exec-time Γ Γᵗ W1 W2 X1 X2 (TSKIP .W1) p2 | .(W1 + 0)
  with +-cancelˡ-≡ W1 eq1
skip-exec-time Γ Γᵗ W1 W2 X1 X2 (TSKIP .W1) p2 | .(W1 + 0) | refl
  with (W2 + X2) in eq2
skip-exec-time Γ Γᵗ W1 W2 _ X2 (TSKIP .W1) (TSKIP .W2)
  | .(W1 + _) | refl | .(W2 + 0) with +-cancelˡ-≡ W2 eq2
... | refl = refl

assign-exec-time : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (S : String) → (e : Aexp {ℕ})
               → (Γ , Γᵗ , W1 =[ Var S := e ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ Var S := e ]=> (W2 + X2))
               → X1 ≡ X2
assign-exec-time Γ Γᵗ W1 W2 X1 X2 S e p1 p2 with (W1 + X1) in eq
assign-exec-time Γ Γᵗ W1 W2 X1 X2 S e (TASSIGN .S n .e .W1) p2 |
  .(W1 + tceval Γᵗ (Var S := e)) with +-cancelˡ-≡ W1 eq
assign-exec-time Γ Γᵗ W1 W2 X1 X2 S e (TASSIGN .S n .e .W1) p2 |
  .(W1 + tceval Γᵗ (Var S := e)) | refl with (W2 + X2) in eq2
assign-exec-time Γ Γᵗ W1 W2 .(Γᵗ S + aeval Γᵗ e) X2 S e (TASSIGN .S n .e .W1)
  (TASSIGN .S n₁ .e .W2) | .(W1 + tceval Γᵗ (Var S := e)) | refl |
  .(W2 + tceval Γᵗ (Var S := e)) with +-cancelˡ-≡ W2 eq2
assign-exec-time Γ Γᵗ W1 W2 .(Γᵗ S + aeval Γᵗ e) X2 S e (TASSIGN .S n .e .W1)
  (TASSIGN .S n₁ .e .W2) | .(W1 + tceval Γᵗ (Var S := e)) | refl |
  .(W2 + tceval Γᵗ (Var S := e)) | refl = refl 

ife-exec-time : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (b : Bexp {ℕ})
               → (t e : Cmd {ℕ}) 
               -- XXX: Note that these two are the same statement here
               → (Γ , Γᵗ , W1 =[ ( IF b THEN t ELSE e END ) ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ ( IF b THEN t ELSE e END ) ]=> (W2 + X2))
               → X1 ≡ X2
ife-exec-time Γ Γᵗ W1 W2 X1 X2 b t e p1 p2
  with (W1 + X1) in eq1 | (W2 + X2) in eq2
ife-exec-time Γ Γᵗ W1 W2 X1 X2 b t e (TIFT n1 .b .t .e .W1 x)
  (TIFT n2 .b .t .e .W2 x₁) | .(W1 + (tceval Γᵗ t + tbeval Γᵗ b))
  | .(W2 + (tceval Γᵗ t + tbeval Γᵗ b)) rewrite +-cancelˡ-≡ W1 eq1
  | +-cancelˡ-≡ W2 eq2 = refl
ife-exec-time Γ Γᵗ W1 W2 X1 X2 b t e (TIFT n1 .b .t .e .W1 x)
  (TIFE n2 .b .t .e .W2 x₁)
  | .(W1 + (tceval Γᵗ t + tbeval Γᵗ b))
  | .(W2 + (tceval Γᵗ e + tbeval Γᵗ b)) = ⊥-elim (contradiction-lemma b Γᵗ x x₁)
ife-exec-time Γ Γᵗ W1 W2 X1 X2 b t e (TIFE n1 .b .t .e .W1 x)
  (TIFT n2 .b .t .e .W2 x₁)
  | .(W1 + (tceval Γᵗ e + tbeval Γᵗ b))
  | .(W2 + (tceval Γᵗ t + tbeval Γᵗ b)) = ⊥-elim (contradiction-lemma b Γᵗ x₁ x)
ife-exec-time Γ Γᵗ W1 W2 X1 X2 b t e (TIFE n1 .b .t .e .W1 x)
  (TIFE n2 .b .t .e .W2 x₁)
  | .(W1 + (tceval Γᵗ e + tbeval Γᵗ b))
  | .(W2 + (tceval Γᵗ e + tbeval Γᵗ b)) rewrite +-cancelˡ-≡ W1 eq1
  | +-cancelˡ-≡ W2 eq2 = refl

-- command lemma: starting from any value the command c takes X amount
-- of time to result in the same execution time TODO: Follow the above
-- and below technique for all command cases!

-- XXX: I will do this at the end because other commands remain.
postulate eq-exec-time : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (c : Cmd {ℕ})
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (Γ , Γᵗ , W1 =[ c ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ c ]=> (W2 + X2))
               → X1 ≡ X2
-- eq-exec-time Γ Γᵗ c W1 W2 X1 X2 p1 p2 = {!!}

seq-exec-time : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (c1 c2 : Cmd {ℕ}) 
               → (Γ , Γᵗ , W1 =[ ( c1 ¿ c2) ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ ( c1 ¿ c2) ]=> (W2 + X2))
               → X1 ≡ X2
seq-exec-time Γ Γᵗ W1 W2 X1 X2 c1 c2 p1 p2 with (W1 + X1) in eq1
  | (W2 + X2) in eq2
seq-exec-time Γ Γᵗ W1 W2 X1 X2 c1 c2 (TSEQ .c1 .c2 .W1 W' W'' p1 p3)
  (TSEQ .c1 .c2 .W2 W''' W'''' p2 p4)
  | .(W1 + (W' + W'')) | .(W2 + (W''' + W''''))
  rewrite +-cancelˡ-≡ W1 eq1 | +-cancelˡ-≡ W2 eq2
  with eq-exec-time Γ Γᵗ c1 W1 W2 W' W''' p1 p2
... | refl
  rewrite 
     +-comm W'''  W''
     | +-comm W1 (W'' + W''')
     | +-assoc W'' W'''  W1
     | +-comm W''' W1
     | +-comm W'' (W1 + W''')
     | +-comm W'''  W''''
     | +-comm W2 (W'''' + W''')
     | +-assoc W'''' W'''  W2
     | +-comm W''' W2
     | +-comm W'''' (W2 + W''')
   with (W1 + W''') | (W2 + W''')
... | l | m
   with eq-exec-time Γ Γᵗ c2 l m W'' W'''' p3 p4
... | refl  = refl




-- Soundness theorem for Seq WCET rule
seq-sound : (Γ : String → Maybe (ProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (c1 c2 : Cmd {ℕ})
            → (W X1 X2 W' : ℕ)
            → (cmd : Γ , Γᵗ , W =[ c1 ¿ c2 ]=> W')
            → (p1 : Γ , Γᵗ , W =[ c1 ]=> (W + X1))
            → (p2 : Γ , Γᵗ , W =[ c2 ]=> (W + X2))
            → (W' ≡ W + (X1 + X2))
seq-sound Γ Γᵗ c1 c2 W X1 X2 .(W + (W' + W''))
  (TSEQ .c1 .c2 .W W' W'' cmd cmd₁) p1 p2
  with Δ-exec Γ Γᵗ W (W + W') (W + X1) c1 cmd p1
... | q with +-cancelˡ-≡ W q
... | refl rewrite +-comm W (X1 + W'') | +-comm X1 W'' | +-assoc W'' X1 W
    | +-comm X1 W | +-comm W'' (W + X1) | +-comm X1 X2 | +-comm W (X2 + X1)
    | +-assoc X2 X1 W | +-comm X2 (X1 + W) | +-comm X1 W with (W + X1)
... | rl with eq-exec-time Γ Γᵗ c2 rl W W'' X2 cmd₁ p2
... | refl = refl


-- Helping lemma for ife
plus-≤ : ∀ (m n p : ℕ) → (m ≤ n) → (m + p) ≤ (n + p)
plus-≤ .zero n p z≤n = m≤n+m p n
plus-≤ .(suc _) .(suc _) p (s≤s {m} {n} q) with plus-≤ m n p q
... | H0 = s≤s H0

plus-> : ∀ (m n p : ℕ) → ((m ≤ n) → ⊥) → (n + p) ≤ (m + p)
plus-> m n p q = {!!}

-- Soundness theorem for If-else WCET rule
ife-sound : (Γ : String → Maybe (ProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (t e : Cmd {ℕ})
            → (b : Bexp {ℕ})
            → (W W' : ℕ)
            → (cmd : Γ , Γᵗ , W =[ (IF b THEN t ELSE e END) ]=> W')
            → (W' ≤ W + ((max (tceval Γᵗ t) (tceval Γᵗ e)) + (tbeval Γᵗ b)))
ife-sound Γ Γᵗ t e b W .(W + (tceval Γᵗ t + tbeval Γᵗ b)) (TIFT n1 .b .t .e .W x)
 with (tceval Γᵗ t) ≤? (tceval Γᵗ e)
... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = ≤-refl
... | true Relation.Nullary.because Relation.Nullary.ofʸ p
  with (tceval Γᵗ t) | (tceval Γᵗ e) | (tbeval Γᵗ b)
... | m | n | q rewrite +-comm W (m + q)
    | +-assoc m q W
    | +-comm W (n + q)
    | +-assoc n q W = plus-≤ m n (q + W) p
ife-sound Γ Γᵗ t e b W .(W + (tceval Γᵗ e + tbeval Γᵗ b)) (TIFE n1 .b .t .e .W x) with (tceval Γᵗ t) ≤? (tceval Γᵗ e)
ife-sound Γ Γᵗ t e b W .(W + (tceval Γᵗ e + tbeval Γᵗ b))
  (TIFE n1 .b .t .e .W x)
  | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p
  with (tceval Γᵗ t) | (tceval Γᵗ e) | (tbeval Γᵗ b)
... | m | n | q rewrite +-comm W (n + q)
    | +-assoc n q W
    | +-comm W (m + q)
    | +-assoc m q W = plus-> m n (q + W) ¬p
ife-sound Γ Γᵗ t e b W .(W + (tceval Γᵗ e + tbeval Γᵗ b))
  (TIFE n1 .b .t .e .W x)
  | true Relation.Nullary.because Relation.Nullary.ofʸ p = ≤-refl

-- Now do loop here

-- Then do exec statement for 1 function call


