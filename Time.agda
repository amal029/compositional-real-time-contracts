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
open import Function.Base using (_$_)

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


-- Making the tuple type needed to hold the program
data TProgTuple {A : Set} : Set where
  _,_,_,_ : (a : ATuple) → (r : RTuple) → (c : Cmd {A}) → (cmt : ℕ) → TProgTuple

-- Getting stuff from the TProgTuple
getProgCmdT : {A : Set} → (p : Maybe (TProgTuple {A})) → Cmd {A}
getProgCmdT (just (_ , _ , c , _)) = c
getProgCmdT nothing = SKIP       -- Dangerous

getProgArgsT : {A : Set} → (p : Maybe (TProgTuple {A})) → ATuple 
getProgArgsT (just (a , _ , _ , _)) = a
getProgArgsT nothing = Arg "VOID"

getProgRetsT : {A : Set} → (p : Maybe (TProgTuple {A})) → RTuple 
getProgRetsT (just (_ , r , _ , _)) = r
getProgRetsT nothing = Ret "VOID"

getProgTimeT : {A : Set} → (p : Maybe (TProgTuple {A})) → ℕ
getProgTimeT (just (_ , _ , _ , t)) = t
getProgTimeT nothing = 0


data _,_=[_]=>ᴬ_  (Γ : (String → ℕ)) : ℕ → (ATuple) → ℕ → Set where

  hd : ∀ (W : ℕ) → ∀ (v : String) →
       Γ , W =[ Arg v ]=>ᴬ (W + (Γ "arg-copy"))

  tl : (l r : ATuple) → (W W' W'' : ℕ) →
       (Γ , W =[ l ]=>ᴬ (W + W')) → (Γ , W + W' =[ r ]=>ᴬ (W + W' + W'')) →
        -----------------------------------------------------------
        Γ , W =[ (l ,` r) ]=>ᴬ (W + W' + W'')

numargs : ∀ (args : ATuple) → ℕ
numargs (Arg v) = 1
numargs (args ,` args₁) = numargs args + numargs args₁

-- soundness theorem for arg copy
args-sound : ∀ (Γ : (String → ℕ)) → ∀ (args : ATuple) → (W W' : ℕ)
             → (Γ , W =[ args ]=>ᴬ W')
             → (W + numargs args * (Γ "arg-copy")) ≡ W'
args-sound Γ .(Arg v) W .(W + Γ "arg-copy") (hd .W v)
  rewrite +-comm (Γ "arg-copy") 0 = refl
args-sound Γ .(l ,` r) W .(W + W' + W'') (tl l r .W W' W'' cmd cmd₁)
  with (Γ "arg-copy") in eq
... | u rewrite *-distribʳ-+ u (numargs l) (numargs r)
    | +-comm W (((numargs l) * u) + ((numargs r) * u))
    | +-comm ((numargs l) * u) ((numargs r) * u)
    | +-assoc ((numargs r) * u) ((numargs l) * u) W
    | +-comm ((numargs l) * u) W
    | +-comm ((numargs r) * u) (W + ((numargs l) * u))
    with args-sound Γ l W (W + W') cmd
... | j with args-sound Γ r (W + W') (W + W' + W'') cmd₁
... | k with +-cancelˡ-≡ W j | +-cancelˡ-≡ (W + W') k | eq
... | refl | refl | refl = refl


data _,_=[_]=>ᴿ_  (Γ : (String →  ℕ)) : ℕ → RTuple → ℕ  → Set where
  hd : ∀ (W : ℕ) → ∀ (v : String) →
       Γ , W =[ Ret v ]=>ᴿ (W + (Γ "ret-copy"))

  tl : (l r : RTuple) → (W W' W'' : ℕ) →
       (Γ , W =[ l ]=>ᴿ (W + W')) → (Γ , W + W' =[ r ]=>ᴿ (W + W' + W'')) →
        -----------------------------------------------------------
        Γ , W =[ (l ,` r) ]=>ᴿ (W + W' + W'')

numrets : ∀ (rets : RTuple) → ℕ
numrets (Ret v) = 1
numrets (rets ,` rets₁) = numrets rets + numrets rets₁

-- soundness theorem for ret copy
rets-sound : ∀ (Γ : (String → ℕ)) → ∀ (rets : RTuple) → (W W' : ℕ)
             → Γ , W =[ rets ]=>ᴿ W'
             → (W + numrets rets * (Γ "ret-copy")) ≡ W'
rets-sound Γ .(Ret v) W .(W + Γ "ret-copy") (hd .W v)
  rewrite +-comm (Γ "ret-copy") 0 = refl
rets-sound Γ .(l ,` r) W .(W + W' + W'') (tl l r .W W' W'' cmd cmd₁)
  with (Γ "ret-copy") in eq
... | u rewrite *-distribʳ-+ u (numrets l) (numrets r)
    | +-comm W (((numrets l) * u) + ((numrets r) * u))
    | +-comm ((numrets l) * u) ((numrets r) * u)
    | +-assoc ((numrets r) * u) ((numrets l) * u) W
    | +-comm ((numrets l) * u) W
    | +-comm ((numrets r) * u) (W + ((numrets l) * u))
    with rets-sound Γ l W (W + W') cmd
... | j with rets-sound Γ r (W + W') (W + W' + W'') cmd₁
... | k with +-cancelˡ-≡ W j | +-cancelˡ-≡ (W + W') k | eq
... | refl | refl | refl = refl

mutual
-- Semantics of time from here
 data _,_,_=[_]=>_ (Γ : (String → Maybe (TProgTuple {ℕ}))) (st : String → ℕ) :
           ℕ → Cmd {ℕ} → ℕ → Set where
  TSKIP : ∀ (W : ℕ) → Γ , st , W =[ SKIP ]=> (W + 0)

  TASSIGN : ∀ (X : String) → ∀ (n : ℕ) → ∀ (e : Aexp {ℕ})
           → ∀ (W : ℕ) →
           ---------------------------------
           Γ , st ,  W =[ (Var X := e) ]=> (W + (taeval st e) + (st "store"))

  TSEQ : ∀ (c1 c2 : Cmd {ℕ})
        → ∀ (W W' W'' : ℕ)
        → Γ , st , W =[ c1 ]=> (W + W')
        → Γ , st , (W + W') =[ c2 ]=> (W + (W' + W'')) →
        --------------------------------------------
        Γ , st ,  W =[ c1 ; c2 ]=> (W + (W' + W''))

  -- XXX: Hack, st contains both exec time and state!
  TIFT : (n1 : ℕ) → (b : Bexp {ℕ}) →
        (t e : Cmd {ℕ}) → ∀ (W W' W'' : ℕ)
        → (beval st b ≡ true)
        → Γ , st , W =[ t ]=> (W + W')
        → Γ , st , W =[ e ]=> (W + W'')
        → Γ , st , W =[ (IF b THEN t ELSE e END) ]=>
          (W + W' + (tbeval st b))

  TIFE : (n1 : ℕ) → (b : Bexp {ℕ}) →
        (t e : Cmd {ℕ}) → ∀ (W W' W'' : ℕ)
        → (beval st b ≡ false)
        → Γ , st , W =[ t ]=> (W + W')
        → Γ , st , W =[ e ]=> (W + W'')
        → Γ , st , W =[ (IF b THEN t ELSE e END) ]=>
          (W +  W'' + (tbeval st b))

  TLF :  (b : Bexp {ℕ}) → (c : Cmd {ℕ}) →
        beval st b ≡ false →
        ∀ (W : ℕ) →
        -----------------------------------------------------------
        Γ , st , W =[ (WHILE b DO c END) ]=>
        (W + 0 + (tbeval st b))

  TLT :  (b : Bexp {ℕ}) → (c : Cmd {ℕ}) →
        beval st b ≡ true → ∀ (W W' : ℕ) →
        -----------------------------------------------------------
        Γ , st , W =[ c ]=> (W + W') →
        Γ , st , W =[ (WHILE b DO c END) ]=>
        (W + ((st "loop-count") * (W' + (tbeval st b))) + (tbeval st b))

 -- CEX : ∀ (f : FuncCall {ℕ}) → ∀ (st st' : (String → ℕ))
 --       → Γ , st =[ f ]=>ᶠ st'
 --       -----------------------------------------------------------
 --       → Γ , st =[ EXEC f ]=> st'
        
 data _,_,_=[_]=>ᶠ_ (Γ : String → (Maybe (TProgTuple {ℕ})))
                    (st : String → ℕ) :
                    ℕ → FuncCall {ℕ} → ℕ → Set where

  Base : ∀ (fname : String) →        -- name of the function
         ∀ (W W' W'' W''' : ℕ)

         -- time to put args on function stack
         → st , W =[ getProgArgsT (Γ fname) ]=>ᴬ (W + W') 

         -- Proof that WCET is what we have in the tuple
         → (wcet-is : (getProgTimeT (Γ fname)) ≡ W'')
         -- time to run the function
         → Γ , st , (W + W') =[ getProgCmdT (Γ fname) ]=> (W + W' + W'')

         -- copying ret values back on caller' stack
         → st , (W + W' + W'')
              =[ getProgRetsT (Γ fname) ]=>ᴿ (W + W' + W'' + W''')

         -----------------------------------------------------------
         → Γ , st , W =[ < getProgRetsT (Γ fname) >:=
             fname < getProgArgsT (Γ fname) > ]=>ᶠ (W + W' + W'' + W''')

  PAR : ∀ (l r : FuncCall {ℕ}) → ∀ (W X1 X2 : ℕ)
        → Γ , st , W =[ l ]=>ᶠ (W + X1)
        → Γ , st , W =[ r ]=>ᶠ (W + X2)
        -----------------------------------------------------------
        → Γ , st , W =[ l ||` r ]=>ᶠ (W + (max X1 X2) + ((2 * (st "fork"))
                                        + (2 * (st "join"))))

-- Soundness theorem for SKIP WCET rule
skip-sound : (Γ : String → Maybe (TProgTuple {ℕ}))
           → (Γᵗ : String → ℕ)  -- map of labels to execution times
           → ∀ (W W' X : ℕ) → (cmd : Γ , Γᵗ , W =[ SKIP ]=> W')
           → (W ≡ X) → (W' ≡ X)
skip-sound Γ Γᵗ W .(W + 0) .W (TSKIP .W) refl rewrite +-comm W 0 = refl

-- Soundness theorem for Assign WCET rule
assign-sound : (Γ : String → Maybe (TProgTuple {ℕ}))
             → (Γᵗ : (String → ℕ))
             → (S : String) → (e : Aexp {ℕ})
             → (W W' : ℕ) → (cmd : Γ , Γᵗ , W =[ Var S := e ]=> W')
             → (W' ≡ W + (taeval Γᵗ e) + (Γᵗ "store"))
assign-sound Γ Γᵗ S e W .(W + taeval Γᵗ e + Γᵗ "store") (TASSIGN .S n .e .W)
  = refl


-- Deterministic exec
Δ-exec : (Γ : String → Maybe (TProgTuple {ℕ}))
         → (Γᵗ : String → ℕ)
         → ∀ (W W' W'' : ℕ) → (c1 : Cmd {ℕ})
         → (Γ , Γᵗ , W =[ c1 ]=> W')
         → (Γ , Γᵗ , W =[ c1 ]=> W'')
         → W' ≡ W''
Δ-exec Γ Γᵗ W .(W + taeval Γᵗ e + Γᵗ "store")
  .(W + taeval Γᵗ e + Γᵗ "store") (Var X := e) (TASSIGN .X n₁ .e .W)
  (TASSIGN .X n .e .W) = refl
Δ-exec Γ Γᵗ W .(W + 0) .(W + 0) .SKIP (TSKIP .W) (TSKIP .W) = refl
Δ-exec Γ Γᵗ W .(W + (W' + W''')) .(W + (W'' + W''''))
 .(c1 ; c2) (TSEQ c1 c2 .W W' W''' p1 p3) (TSEQ .c1 .c2 .W W'' W'''' p2 p4)
 with Δ-exec Γ Γᵗ W (W + W') (W + W'') c1 p1 p2
... | r with +-cancelˡ-≡ W r
... | refl
 with Δ-exec Γ Γᵗ (W + W') (W + (W' + W''')) (W + (W' + W'''')) c2 p3 p4
... | rr with +-cancelˡ-≡ W rr
... | rm with +-cancelˡ-≡ W' rm
... | refl = refl
Δ-exec Γ Γᵗ W .(W + 0 + tbeval Γᵗ b)
  .(W + 0 + tbeval Γᵗ b) WHILE b DO c END (TLF .b .c x .W)
  (TLF .b .c x₁ .W) = refl
Δ-exec Γ Γᵗ W .(W + Γᵗ "loop-count" * (W' + tbeval Γᵗ b) + _)
  .(W + 0 + tbeval Γᵗ b) WHILE b DO c END (TLT .b .c x .W W' x₂)
  (TLF .b .c x₁ .W) = ⊥-elim (contradiction-lemma b Γᵗ x x₁)
Δ-exec Γ Γᵗ W .(W + 0 + tbeval Γᵗ b)
  .(W + Γᵗ "loop-count" * (W'' + tbeval Γᵗ b) + _) WHILE b DO c END
  (TLF .b .c x .W) (TLT .b .c x₁ .W W'' x₂)
  = ⊥-elim (contradiction-lemma b Γᵗ x₁ x)
Δ-exec Γ Γᵗ W .(W + Γᵗ "loop-count" * (W' + tbeval Γᵗ b) + _)
  .(W + Γᵗ "loop-count" * (W'' + tbeval Γᵗ b) + _) WHILE b DO c END
  (TLT .b .c x .W W' x₃) (TLT .b .c x₁ .W W'' x₂)
  with Δ-exec Γ Γᵗ W (W + W') (W + W'') c x₃ x₂
... | l with +-cancelˡ-≡ W l
... | refl = refl
Δ-exec Γ Γᵗ W .(W + W' + tbeval Γᵗ b)
  .(W + W'' + tbeval Γᵗ b) IF b THEN t ELSE e END
  (TIFT n2 .b .t .e .W W' W'''' x x₄ x₅)
  (TIFT n1 .b .t .e .W W'' W''' x₁ x₂ x₃)
  with Δ-exec Γ Γᵗ W (W + W') (W + W'') t x₄ x₂
... | y with +-cancelˡ-≡ W y
... | refl = refl
Δ-exec Γ Γᵗ W .(W + W'''' + tbeval Γᵗ b)
  .(W + W'' + tbeval Γᵗ b) IF b THEN t ELSE e END
  (TIFE n2 .b .t .e .W W' W'''' x x₄ x₅)
  (TIFT n1 .b .t .e .W W'' W''' x₁ x₂ x₃)
  = ⊥-elim (contradiction-lemma b Γᵗ x₁ x)
Δ-exec Γ Γᵗ W .(W + W' + tbeval Γᵗ b)
  .(W + W''' + tbeval Γᵗ b) IF b THEN t ELSE e END
  (TIFT n2 .b .t .e .W W' W'''' x x₄ x₅)
  (TIFE n1 .b .t .e .W W'' W''' x₁ x₂ x₃)
  = ⊥-elim (contradiction-lemma b Γᵗ x x₁)
Δ-exec Γ Γᵗ W .(W + W'''' + tbeval Γᵗ b)
  .(W + W''' + tbeval Γᵗ b) IF b THEN t ELSE e END
  (TIFE n2 .b .t .e .W W' W'''' x x₄ x₅)
  (TIFE n1 .b .t .e .W W'' W''' x₁ x₂ x₃)
  with Δ-exec Γ Γᵗ W (W + W''') (W + W'''') e x₃ x₅
... | y with +-cancelˡ-≡ W y
... | refl = refl


-- Deterministic execution of a function
Δ-exec-func : (Γ : String → Maybe (TProgTuple {ℕ}))
              → (Γᵗ : String → ℕ) → (l : FuncCall {ℕ})
              → (W W' W'' : ℕ)
              → Γ , Γᵗ , W =[ l ]=>ᶠ W'
              → Γ , Γᵗ , W =[ l ]=>ᶠ W''
              → W' ≡ W''
Δ-exec-func Γ Γᵗ
  .(< getProgRetsT (Γ fname) >:= fname < getProgArgsT (Γ fname) >) W
  .(W + W' + getProgTimeT (Γ fname) + W'''')
  .(W + W'' + getProgTimeT (Γ fname) + W'''''')
  (Base fname .W W' .(getProgTimeT (Γ fname)) W'''' x refl x₁ x₂)
  (Base .fname .W W'' .(getProgTimeT (Γ fname)) W'''''' x₃ refl x₄ x₅)
  with args-sound Γᵗ (getProgArgsT (Γ fname)) W (W + W') x
  | args-sound Γᵗ (getProgArgsT (Γ fname)) W (W + W'') x₃
  | rets-sound Γᵗ (getProgRetsT (Γ fname)) (W + W' + getProgTimeT (Γ fname))
    (W + W' + getProgTimeT (Γ fname) + W'''') x₂
  | rets-sound Γᵗ (getProgRetsT (Γ fname)) (W + W'' + getProgTimeT (Γ fname))
    (W + W'' + getProgTimeT (Γ fname) + W'''''') x₅
... | l | l1 | r1 | r2
  with +-cancelˡ-≡ W l | +-cancelˡ-≡ W l1
... | refl | refl with +-cancelˡ-≡
  (W + numargs (getProgArgsT (Γ fname)) * Γᵗ "arg-copy"
  + getProgTimeT (Γ fname)) r2
... | refl with +-cancelˡ-≡
  (W + numargs (getProgArgsT (Γ fname)) * Γᵗ "arg-copy"
  + getProgTimeT (Γ fname)) r1
... | refl = refl
Δ-exec-func Γ Γᵗ .(l ||` r) W
  .(W + max X1 X2 + (2 * Γᵗ "fork" + 2 * Γᵗ "join"))
  .(W + max X3 X4 + (2 * Γᵗ "fork" + 2 * Γᵗ "join"))
  (PAR l r .W X1 X2 e1 e3) (PAR .l .r .W X3 X4 e2 e4)
  with Δ-exec-func Γ Γᵗ l W (W + X1) (W + X3) e1 e2
  | Δ-exec-func Γ Γᵗ r W (W + X2) (W + X4) e3 e4
... | m | y with +-cancelˡ-≡ W m | +-cancelˡ-≡ W y
... | refl | refl = refl


skip-cancel : ∀ (Γ : String → Maybe (TProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (Γ , Γᵗ , W1 =[ SKIP ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ SKIP ]=> (W2 + X2))
               → X1 ≡ X2
skip-cancel Γ Γᵗ W1 W2 X1 X2 p1 p2 with (W1 + X1) in eq1
skip-cancel Γ Γᵗ W1 W2 X1 X2 (TSKIP .W1) p2 | .(W1 + 0)
  with +-cancelˡ-≡ W1 eq1
skip-cancel Γ Γᵗ W1 W2 X1 X2 (TSKIP .W1) p2 | .(W1 + 0) | refl
  with (W2 + X2) in eq2
skip-cancel Γ Γᵗ W1 W2 _ X2 (TSKIP .W1) (TSKIP .W2)
  | .(W1 + _) | refl | .(W2 + 0) with +-cancelˡ-≡ W2 eq2
... | refl = refl

assign-cancel : ∀ (Γ : String → Maybe (TProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (S : String) → (e : Aexp {ℕ})
               → (Γ , Γᵗ , W1 =[ Var S := e ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ Var S := e ]=> (W2 + X2))
               → X1 ≡ X2
assign-cancel Γ Γᵗ W1 W2 X1 X2 S e cmd1 cmd2 with (W1 + X1) in eq1
  | (W2 + X2) in eq2
assign-cancel Γ Γᵗ W1 W2 X1 X2 S e (TASSIGN .S n .e .W1)
  (TASSIGN .S n₁ .e .W2) | .(W1 + taeval Γᵗ e + Γᵗ "store")
  | .(W2 + taeval Γᵗ e + Γᵗ "store")
  rewrite +-assoc W1 (taeval Γᵗ e) (Γᵗ "store")
  | +-assoc W2 (taeval Γᵗ e) (Γᵗ "store")
  with +-cancelˡ-≡ W1 eq1 | +-cancelˡ-≡ W2 eq2
... | refl | refl = refl

loop-cancel : ∀ (Γ : String → Maybe (TProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (b : Bexp {ℕ})
               → (c : Cmd {ℕ}) 
               → (Γ , Γᵗ , W1 =[ (WHILE b DO c END) ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ (WHILE b DO c END) ]=> (W2 + X2))
               → X1 ≡ X2
ife-cancel : ∀ (Γ : String → Maybe (TProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (b : Bexp {ℕ})
               → (t e : Cmd {ℕ}) 
               → (Γ , Γᵗ , W1 =[ ( IF b THEN t ELSE e END ) ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ ( IF b THEN t ELSE e END ) ]=> (W2 + X2))
               → X1 ≡ X2
seq-cancel : ∀ (Γ : String → Maybe (TProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (c1 c2 : Cmd {ℕ}) 
               → (Γ , Γᵗ , W1 =[ ( c1 ; c2) ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ ( c1 ; c2) ]=> (W2 + X2))
               → X1 ≡ X2

-- The general case of cancellation.
eq-cancel : ∀ (Γ : String → Maybe (TProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (c : Cmd {ℕ})
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (Γ , Γᵗ , W1 =[ c ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ c ]=> (W2 + X2))
               → X1 ≡ X2

loop-cancel Γ Γᵗ W1 W2 X1 X2 b c cmd1 cmd2
  with (W1 + X1) in eq1 | (W2 + X2) in eq2
loop-cancel Γ Γᵗ W1 W2 X1 X2 b c (TLF .b .c x .W1)
  (TLF .b .c x₁ .W2) | .(W1 + 0 + tbeval Γᵗ b) | .(W2 + 0 + tbeval Γᵗ b)
  rewrite +-assoc W1 0 (tbeval Γᵗ b) | +-assoc W2 0 (tbeval Γᵗ b)
  with +-cancelˡ-≡ W1 eq1 | +-cancelˡ-≡ W2 eq2
... | refl | refl = refl
loop-cancel Γ Γᵗ W1 W2 X1 X2 b c (TLF .b .c x .W1)
  (TLT .b .c x₁ .W2 W' cmd2) | .(W1 + 0 + tbeval Γᵗ b)
  | .(W2 + Γᵗ "loop-count" * (W' + tbeval Γᵗ b) + tbeval Γᵗ b)
  = ⊥-elim (contradiction-lemma b Γᵗ x₁ x)
loop-cancel Γ Γᵗ W1 W2 X1 X2 b c (TLT .b .c x .W1 W' cmd1)
  (TLF .b .c x₁ .W2)
  | .(W1 + Γᵗ "loop-count" * (W' + tbeval Γᵗ b) + tbeval Γᵗ b)
  | .(W2 + 0 + tbeval Γᵗ b) = ⊥-elim (contradiction-lemma b Γᵗ x x₁)
loop-cancel Γ Γᵗ W1 W2 X1 X2 b c (TLT .b .c x .W1 W' cmd1)
  (TLT .b .c x₁ .W2 W'' cmd2)
  | .(W1 + Γᵗ "loop-count" * (W' + tbeval Γᵗ b) + tbeval Γᵗ b)
  | .(W2 + Γᵗ "loop-count" * (W'' + tbeval Γᵗ b) + tbeval Γᵗ b)
  with eq-cancel Γ Γᵗ c W1 W2 W' W'' cmd1 cmd2
... | refl with (Γᵗ "loop-count") | (tbeval Γᵗ b)
... | LC | BC rewrite +-assoc W2 (LC * (W' + BC)) BC
    | +-assoc W1 (LC * (W' + BC)) BC
    with +-cancelˡ-≡ W2 eq2 | +-cancelˡ-≡ W1 eq1
... | refl | refl = refl

ife-cancel Γ Γᵗ W1 W2 X1 X2 b t e p1 p2 with (W1 + X1) in eq1
  | (W2 + X2) in eq2
ife-cancel Γ Γᵗ W1 W2 X1 X2 b t e (TIFT n1 .b .t .e .W1 W' W'' x p1 p3)
  (TIFT n2 .b .t .e .W2 W''' W'''' x₁ p2 p4) | .(W1 + W' + tbeval Γᵗ b)
  | .(W2 + W''' + tbeval Γᵗ b) with eq-cancel Γ Γᵗ t W1 W2 W' W''' p1 p2
... | refl rewrite +-assoc W2 W' (tbeval Γᵗ b) | +-assoc W1 W' (tbeval Γᵗ b)
  with +-cancelˡ-≡ W2 eq2 | +-cancelˡ-≡ W1 eq1
... | refl | refl = refl
ife-cancel Γ Γᵗ W1 W2 X1 X2 b t e (TIFT n1 .b .t .e .W1 W' W'' x p1 p3)
  (TIFE n2 .b .t .e .W2 W''' W'''' x₁ p2 p4) | .(W1 + W' + tbeval Γᵗ b)
  | .(W2 + W'''' + tbeval Γᵗ b) = ⊥-elim (contradiction-lemma b Γᵗ x x₁)
ife-cancel Γ Γᵗ W1 W2 X1 X2 b t e (TIFE n1 .b .t .e .W1 W' W'' x p1 p3)
  (TIFT n2 .b .t .e .W2 W''' W'''' x₁ p2 p4) | .(W1 + W'' + tbeval Γᵗ b)
  | .(W2 + W''' + tbeval Γᵗ b) = ⊥-elim (contradiction-lemma b Γᵗ x₁ x)
ife-cancel Γ Γᵗ W1 W2 X1 X2 b t e (TIFE n1 .b .t .e .W1 W' W'' x p1 p3)
  (TIFE n2 .b .t .e .W2 W''' W'''' x₁ p2 p4) | .(W1 + W'' + tbeval Γᵗ b)
  | .(W2 + W'''' + tbeval Γᵗ b) rewrite +-assoc W1 W'' (tbeval Γᵗ b)
  | +-assoc W2 W'''' (tbeval Γᵗ b) with +-cancelˡ-≡ W2 eq2
  | +-cancelˡ-≡ W1 eq1 | eq-cancel Γ Γᵗ e W1 W2 W'' W'''' p3 p4
... | refl | refl | refl = refl

seq-cancel Γ Γᵗ W1 W2 X1 X2 c1 c2 p1 p2 with (W1 + X1) in eq1
  | (W2 + X2) in eq2
seq-cancel Γ Γᵗ W1 W2 X1 X2 c1 c2 (TSEQ .c1 .c2 .W1 W' W'' p1 p3)
  (TSEQ .c1 .c2 .W2 W''' W'''' p2 p4)
  | .(W1 + (W' + W'')) | .(W2 + (W''' + W''''))
  rewrite +-cancelˡ-≡ W1 eq1 | +-cancelˡ-≡ W2 eq2
  with eq-cancel Γ Γᵗ c1 W1 W2 W' W''' p1 p2
... | refl
  rewrite 
     +-comm W'''  W''
     | +-comm W1 (W'' + W''') | +-assoc W'' W'''  W1 | +-comm W''' W1
     | +-comm W'' (W1 + W''') | +-comm W'''  W'''' | +-comm W2 (W'''' + W''')
     | +-assoc W'''' W'''  W2 | +-comm W''' W2 | +-comm W'''' (W2 + W''')
   with (W1 + W''') | (W2 + W''')
... | l | m
   with eq-cancel Γ Γᵗ c2 l m W'' W'''' p3 p4
... | refl  = refl

eq-cancel Γ Γᵗ SKIP W1 W2 X1 X2 p1 p2 = skip-cancel Γ Γᵗ W1 W2 X1 X2 p1 p2
eq-cancel Γ Γᵗ (Var x := r) W1 W2 X1 X2 p1 p2
  = assign-cancel Γ Γᵗ W1 W2 X1 X2 x r p1 p2
eq-cancel Γ Γᵗ (c ; c₁) W1 W2 X1 X2 p1 p2
  = seq-cancel Γ Γᵗ W1 W2 X1 X2 c c₁ p1 p2
eq-cancel Γ Γᵗ IF b THEN c ELSE c₁ END W1 W2 X1 X2 p1 p2
  = ife-cancel Γ Γᵗ W1 W2 X1 X2 b c c₁ p1 p2
eq-cancel Γ Γᵗ WHILE b DO c END W1 W2 X1 X2 p1 p2
  = loop-cancel Γ Γᵗ W1 W2 X1 X2 b c p1 p2

-- TODO: The function call case and concurrency cases will go here

-- Soundness theorem for Seq WCET rule
seq-sound : (Γ : String → Maybe (TProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (c1 c2 : Cmd {ℕ})
            → (W X1 X2 W' : ℕ)
            → (cmd : Γ , Γᵗ , W =[ c1 ; c2 ]=> W')
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
... | rl with eq-cancel Γ Γᵗ c2 rl W W'' X2 cmd₁ p2
... | refl = refl


-- Helping lemma for ife
plus-≤ : ∀ (m n p : ℕ) → (m ≤ n) → (m + p) ≤ (n + p)
plus-≤ .zero n p z≤n = m≤n+m p n
plus-≤ .(suc _) .(suc _) p (s≤s {m} {n} q) with plus-≤ m n p q
... | H0 = s≤s H0

≤-rela1 : ∀ (m n : ℕ) → ¬ (m ≤ n) → (n < m)
≤-rela1 zero n p = ⊥-elim (p z≤n)
≤-rela1 (suc m) zero p = s≤s z≤n
≤-rela1 (suc m) (suc n) p = s≤s (≤-rela1 m n (λ z → p (s≤s z)))

≤-rela2 : ∀ (m n : ℕ) → (suc n ≤ m) → (n ≤ m)
≤-rela2 m n p with n≤1+n n
... | q = ≤-trans q p

-- if-helper
if-helper : ∀ (X1 X2 : ℕ) → (X1 ≤ max X1 X2)
if-helper X1 X2 with (X1 ≤? X2)
... | false Relation.Nullary.because proof = ≤′⇒≤ ≤′-refl
... | true Relation.Nullary.because Relation.Nullary.ofʸ p = p

if-helper2 : ∀ (X1 X2 : ℕ) → (X2 ≤ max X1 X2)
if-helper2 X1 X2 with (X1 ≤? X2)
if-helper2 X1 X2 | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p
  with ≤-rela1 X1 X2 (¬p)
... | q = ≤-rela2 X1 X2 q
if-helper2 X1 X2 | true Relation.Nullary.because _ = ≤′⇒≤ ≤′-refl

-- Soundness theorem for If-else WCET rule
ife-sound : (Γ : String → Maybe (TProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (t e : Cmd {ℕ})
            → (b : Bexp {ℕ})
            → (W X1 X2 W' : ℕ)
            → (tcmd : Γ , Γᵗ , W =[ t ]=> (W + X1))
            → (ecmd : Γ , Γᵗ , W =[ e ]=> (W + X2))
            → (cmd : Γ , Γᵗ , W =[ (IF b THEN t ELSE e END) ]=> W')
            → (W' ≤ W + (max X1 X2) + (tbeval Γᵗ b))
ife-sound Γ Γᵗ t e b W X1 X2 .(W + W' + tbeval Γᵗ b) tcmd ecmd
  (TIFT n1 .b .t .e .W W' W'' x cmd cmd₁)
  with Δ-exec Γ Γᵗ W (W + W') (W + X1) t cmd tcmd
... | l with +-cancelˡ-≡ W l
... | refl rewrite +-assoc W X1 (tbeval Γᵗ b) | +-comm W (X1 + (tbeval Γᵗ b))
    | +-assoc X1 (tbeval Γᵗ b) W with (tbeval Γᵗ b)
... | Y with max X1 X2 in eq
... | M rewrite +-assoc W M Y | +-comm W (M + Y) | +-assoc M Y W
    with (Y + W)
... | L with if-helper X1 X2 | eq
... | T | refl = plus-≤ X1 M L T
ife-sound Γ Γᵗ t e b W X1 X2 .(W + W'' + tbeval Γᵗ b) tcmd ecmd
  (TIFE n1 .b .t .e .W W' W'' x cmd cmd₁)
  with (tbeval Γᵗ b) | Δ-exec Γ Γᵗ W (W + W'') (W + X2) e cmd₁ ecmd
... | Y | l with +-cancelˡ-≡ W l
... | refl with max X1 X2 in eq
... | M rewrite +-assoc W X2 Y | +-assoc W M Y | +-comm W (X2 + Y)
    | +-comm W (M + Y) | +-assoc X2 Y W | +-assoc M Y W with (Y + W)
... | L with if-helper2 X1 X2 | eq
... | T | refl = plus-≤ X2 M L T

-- Helper for loop
loop-helper : ∀ (l g : ℕ) → (l ≤′ (g + l))
loop-helper l zero = ≤′-refl
loop-helper l (suc g) = ≤′-step (loop-helper l g)

-- XXX: Using well founded recursion here
loop-sound-≤′ : (Γ : String → Maybe (TProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (c : Cmd {ℕ})
            → (b : Bexp {ℕ})
            → (W W' X1 : ℕ)
            → (Γ , Γᵗ , W =[ c ]=> (W + X1))
            → (cmd : Γ , Γᵗ , W =[ (WHILE b DO c END) ]=> W')
            → W' ≤′
              W + ((Γᵗ "loop-count") * (X1 + (tbeval Γᵗ b))) + (tbeval Γᵗ b)
loop-sound-≤′ Γ Γᵗ c b W .(W + 0 + tbeval Γᵗ b) X1 cmd (TLF .b .c x .W)
  with (Γᵗ "loop-count")
... | zero = ≤′-refl
... | suc m rewrite +-comm W 0
    with (tbeval Γᵗ b)
... | q
    with (X1 + q + m * (X1 + q))
... | t rewrite +-comm W t | +-assoc t W q with (W + q)
... | l = loop-helper l t
loop-sound-≤′  Γ Γᵗ c b W
  .(W + Γᵗ "loop-count" * (W' + tbeval Γᵗ b) + tbeval Γᵗ b) X1 cmd
  (TLT .b .c x .W W' cmd1)
  with Δ-exec Γ Γᵗ W (W + W') (W + X1) c cmd1 cmd
... | r with +-cancelˡ-≡ W r
... | refl = ≤′-refl

-- The general case 
loop-sound : (Γ : String → Maybe (TProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (c : Cmd {ℕ})
            → (b : Bexp {ℕ})
            → (W W' X1 : ℕ)
            → (Γ , Γᵗ , W =[ c ]=> (W + X1))
            → (cmd : Γ , Γᵗ , W =[ (WHILE b DO c END) ]=> W')
            → W' ≤
              W + ((Γᵗ "loop-count") * (X1 + (tbeval Γᵗ b))) + (tbeval Γᵗ b)
loop-sound Γ Γᵗ c b W W' X1 c2 cmd =
  ≤′⇒≤ (loop-sound-≤′ Γ Γᵗ c b W W' X1 c2 cmd)


-- The soundness theorem for a single function call
func-sound : (Γ : String → Maybe (TProgTuple {ℕ})) → ∀ (Γᵗ : String → ℕ)
             → ∀ (fname : String) → ∀ (W W' : ℕ)
             → Γ , Γᵗ , W =[ < getProgRetsT (Γ fname) >:=
                             fname < getProgArgsT (Γ fname) > ]=>ᶠ W'
             → W' ≡ (W +
                       ((numargs $ getProgArgsT $ (Γ fname)) * (Γᵗ "arg-copy"))
                    + (getProgTimeT (Γ fname))
                    + ((numrets $ getProgRetsT $ (Γ fname)) * (Γᵗ "ret-copy")))
func-sound Γ Γᵗ fname W .(W + W' + getProgTimeT (Γ fname) + W''')
  (Base .fname .W W' .(getProgTimeT (Γ fname)) W''' x refl x₁ x₂)
  with args-sound Γᵗ (getProgArgsT (Γ fname)) W (W + W') x
       | rets-sound Γᵗ (getProgRetsT (Γ fname))
         (W + W' + getProgTimeT (Γ fname))
         (W + W' + getProgTimeT (Γ fname) + W''') x₂
... | l | m with +-cancelˡ-≡ W l
... | refl
  with +-cancelˡ-≡ (W + numargs (getProgArgsT (Γ fname)) * Γᵗ "arg-copy"
                   + getProgTimeT (Γ fname)) m
... | refl = refl

-- The soundness theorem for PAR (||`) execution of threads
par-sound : (Γ : String → Maybe (TProgTuple {ℕ})) → ∀ (Γᵗ : String → ℕ)
            → (l r : FuncCall {ℕ}) → (W W' X1 X2 : ℕ)
            → Γ , Γᵗ , W =[ l ||` r ]=>ᶠ W'
            → Γ , Γᵗ , W =[ l ]=>ᶠ (W + X1)
            → Γ , Γᵗ , W =[ r ]=>ᶠ (W + X2)
            → W' ≡ W + (max X1 X2) + 2 * ((Γᵗ "fork") + (Γᵗ "join"))
par-sound Γ Γᵗ l r W .(W + max X3 X4 + (2 * Γᵗ "fork" + 2 * Γᵗ "join"))
  X1 X2 (PAR .l .r .W X3 X4 pare pare₁) parl parr
  with (Γᵗ "fork") | (Γᵗ "join")
... | tf | tj rewrite *-distribˡ-+ 2 tf tj
    | +-assoc tf tj 0 | +-comm tj 0 | +-comm tf 0
    | +-assoc tf tj (tf + tj) | +-comm tj (tf + tj)
    | +-assoc tf tj tj | +-comm tf (tf + (tj + tj))
    | +-comm tf (tj + tj) with (tf + tf + (tj + tj))
... | m with Δ-exec-func Γ Γᵗ l W (W + X1) (W + X3) parl pare
... | q with Δ-exec-func Γ Γᵗ r W (W + X2) (W + X4) parr pare₁
... | q2 with +-cancelˡ-≡ W q | +-cancelˡ-≡ W q2
... | refl | refl = refl
