-- {-# OPTIONS --safe #-}
module Time where

open import Map
open import Relation.Binary.PropositionalEquality
open import Data.String using (String)
open import Data.Nat
open import Data.Nat.Base using (_≤_)
open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_)
open import Data.List
open import Data.Nat.Properties

-- I separated this because of function calls
data VarId : Set where
  Var : (x : String) → VarId

-- This is the language of expressions
data Aexp {A : Set} : Set where
  _+`_ : ∀(x1 x2 : Aexp {A}) → Aexp
  _-`_ : ∀(x1 x2 : Aexp {A}) → Aexp
  _*`_ : ∀(x1 x2 : Aexp {A}) → Aexp
  Avar : ∀(x : String) → Aexp
  Anum : ∀(x : A) → Aexp
  -- Type A should be comparable to 0
  -- _/_ : ∀(x1 x2 : A) → (x2 ≡ 0) → Aexp

-- Special - for ℕ
_~-~_ : (a b : ℕ) → ℕ
zero ~-~ b = 0
suc a ~-~ b = a ~-~ b

-- Evaluation of Arithexp
aeval : (st : String → ℕ) → (exp : Aexp {ℕ}) → ℕ
aeval st (e +` e₁) = aeval st e + aeval st e₁
aeval st (e -` e₁) = aeval st e ~-~ aeval st e₁
aeval st (e *` e₁) = aeval st e * aeval st e₁
aeval st (Avar x) = st x
aeval st (Anum x) = x

-- This is the language of boolean expressions
data Bexp {A : Set} : Set where
  TRUE : Bexp
  FALSE : Bexp
  _<`_ : ∀ (x1 x2 : Aexp {A}) → Bexp
  _>`_ : ∀ (x1 x2 : Aexp {A}) → Bexp
  _≤`_ : ∀ (x1 x2 : Aexp {A}) → Bexp
  _≥`_ : ∀ (x1 x2 : Aexp {A}) → Bexp
  _≡`_ : ∀ (x1 x2 : Aexp {A}) → Bexp
  ¬`_ : ∀ (b : Bexp {A}) → Bexp
  _&&`_ : ∀ (b1 b2 : Bexp {A}) → Bexp
  _||`_ : ∀ (b1 b2 : Bexp {A}) → Bexp


-- Bool evaluation for ℕ
beval : (st : String → ℕ) → (b : Bexp {ℕ}) → Bool
beval st TRUE = true
beval st FALSE = false
beval st (x1 <` x2) = let ql = aeval st x1 in
                       let qr = aeval st x2 in
                       ((not ((ql ≤ᵇ qr) ∧ (qr ≤ᵇ ql))) ∧ (ql ≤ᵇ qr))
beval st (x1 >` x2) = let ql = aeval st x1 in
                       let qr = aeval st x2 in
                       ((not ((ql ≤ᵇ qr) ∧ (qr ≤ᵇ ql))) ∧ (qr ≤ᵇ ql))
beval st (x1 ≤` x2) = let l = aeval st x1 in
                       let r = aeval st x2 in
                       l ≤ᵇ r
beval st (x1 ≥` x2) = let l = aeval st x1 in
                       let r = aeval st x2 in
                       r ≤ᵇ l
beval st (x1 ≡` x2) = let l = aeval st x1 in
                       let r = aeval st x2 in
                       (l ≤ᵇ r) ∧ (r ≤ᵇ l)
beval st (¬` b) = not (beval st b)
beval st (b &&` b₁) = beval st b ∧ beval st b₁
beval st (b ||` b₁) = beval st b ∨ beval st b₁


data ATuple : Set where
  Arg : (v : String) → ATuple
  _,`_ : (f : ATuple) → (n : ATuple) → ATuple

data RTuple : Set where
  Ret : (v : String) → RTuple
  _,`_ : (f : RTuple) → (n : RTuple) → RTuple

-- Name of functions are in different namespace
data FuncCall {A : Set} : Set where
  -- Calling a function
  <_>:=_<_> : (ret : RTuple) → (f : String) →
              (args : ATuple) → FuncCall
  -- XXX: Note that the below allows writing code like
  -- this: F()||F()//F()
  _||`_ : (l r : FuncCall {A}) → FuncCall
  _//`_ : (l r : FuncCall {A}) → FuncCall

-- This is the command language that we have
data Cmd {A : Set} : Set where
  SKIP : Cmd
  _:=_ : (l : VarId) → (r : Aexp {A}) → Cmd
  _¿_ : (c1 c2 : Cmd {A}) → Cmd
  IF_THEN_ELSE_END : (b : Bexp {A}) → (t : Cmd {A}) →
                   (c : Cmd {A}) → Cmd
  WHILE_DO_END : (b : Bexp {A}) → (bo : Cmd {A}) → Cmd

  -- This makes calling the function a command
  EXEC : FuncCall {A} → Cmd

-- This is defining a function
-- This should give state of type (f → Maybe (Ret strings, args string, Cmd))
-- This should be an eval function, not a relation
-- This will be called from funccall and go from st => st'
data FuncDef {A : Set} : Set where
  -- Define a function/thread
  DEF_<_>⇒<_>:_END : (f : String) → (ATuple)
                   → (RTuple) → (c : Cmd {A}) → FuncDef

-- Toplevel
-- This should start from MAIN
-- This should be an topeval function KP => st
data Top {A : Set} : Set where
  MAIN:_END :  (c : Cmd {A}) → Top
  _¿_ : FuncDef {A} → (a : Top {A}) → Top
  

infix 22 _:=_
infixl 21 _¿_ 
infixl 20 _||`_
infixl 20 _//`_
infixl 23 _-`_
infixl 23 _+`_
infixl 24 _*`_
infixl 25 _,`_                  -- Highest precedence and left assoc

-- Making the tuple type needed to hold the program
data ProgTuple {A : Set} : Set where
  _,_,_ : (a : ATuple) → (r : RTuple) → (c : Cmd {A}) → ProgTuple


-- Getting stuff from the Progtuple
getProgCmd : {A : Set} → (p : Maybe (ProgTuple {A})) → Cmd {A}
getProgCmd (just (a , r , c)) = c
getProgCmd nothing = SKIP       -- Dangerous

getProgArgs : {A : Set} → (p : Maybe (ProgTuple {A})) → ATuple 
getProgArgs (just (a , r , c)) = a
getProgArgs nothing = Arg "VOID"

getProgRets : {A : Set} → (p : Maybe (ProgTuple {A})) → RTuple 
getProgRets (just (a , r , c)) = r
getProgRets nothing = Ret "VOID"

-- The max function needed for WCET
max : ∀ (m n : ℕ) → ℕ
max m n with m Data.Nat.≤ᵇ n
... | false = n
... | true = m

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

 TIF : ∀ (n1 : ℕ) → (b : Bexp {ℕ}) → (t e : Cmd {ℕ}) → ∀ (W : ℕ) →
       -----------------------------------------------------------
        Γ , st , W =[ (IF b THEN t ELSE e END) ]=>
          (W + (tceval st (IF b THEN t ELSE e END) + (tbeval st b)))

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
evalProg : {A : Set} → (p : Top {A}) →
           (st : String → Maybe (ProgTuple {A})) →
           (String → Maybe (ProgTuple {A}))
evalProg MAIN: c END st = (StoreP st "MAIN" (Arg "void" , Ret "void" , c))
evalProg (DEF f < x >⇒< x1 >: c END ¿ p) st =
              StoreP (evalProg p st) f (x , x1 , c)


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
Δ-exec Γ Γᵗ W .(W + tceval Γᵗ (Var X := e)) .(W + tceval Γᵗ (Var X := e)) .(Var X := e) (TASSIGN X n e .W) (TASSIGN .X n₁ .e .W) = refl
Δ-exec Γ Γᵗ W .(W + (W' + W''')) .(W + (W'' + W'''')) .(c1 ¿ c2) (TSEQ c1 c2 .W W' W''' p1 p3) (TSEQ .c1 .c2 .W W'' W'''' p2 p4)
 with Δ-exec Γ Γᵗ W (W + W') (W + W'') c1 p1 p2
... | r with +-cancelˡ-≡ W r
... | refl
 with Δ-exec Γ Γᵗ (W + W') (W + (W' + W''')) (W + (W' + W'''')) c2 p3 p4
... | rr with +-cancelˡ-≡ W rr
... | rm with +-cancelˡ-≡ W' rm
... | refl = refl
Δ-exec Γ Γᵗ W .(W + (tceval Γᵗ IF b THEN t ELSE e END + tbeval Γᵗ b)) .(W + (tceval Γᵗ IF b THEN t ELSE e END + tbeval Γᵗ b)) .(IF b THEN t ELSE e END) (TIF n1 b t e .W) (TIF n2 .b .t .e .W) = refl


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
skip-exec-time Γ Γᵗ W1 W2 _ X2 (TSKIP .W1) (TSKIP .W2) | .(W1 + _) | refl | .(W2 + 0) with +-cancelˡ-≡ W2 eq2
... | refl = refl


-- command lemma: starting from any value the command c takes X amount
-- of time to result in the same execution time
-- TODO: Follow the above technique for all cases!
postulate eq-exec-time : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
               → (Γᵗ : String → ℕ)
               → ∀ (c : Cmd {ℕ})
               → ∀ (W1 W2 X1 X2 : ℕ)
               → (Γ , Γᵗ , W1 =[ c ]=> (W1 + X1))
               → (Γ , Γᵗ , W2 =[ c ]=> (W2 + X2))
               → X1 ≡ X2
-- eq-exec-time Γ Γᵗ c W1 W2 X1 X2 p1 p2 = {!!}



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

-- Soundness theorem for If-else WCET rule
ife-sound : (Γ : String → Maybe (ProgTuple {ℕ}))
            → (Γᵗ : String → ℕ)
            → (t e : Cmd {ℕ})
            → (b : Bexp {ℕ})
            → (W X1 X2 W' : ℕ)
            → (cmd : Γ , Γᵗ , W =[ (IF b THEN t ELSE e END) ]=> W')
            → (tceval Γᵗ t ≡ X1)
            → (tceval Γᵗ e ≡ X2)
            → (W' ≡ W + ((max X1 X2) + (tbeval Γᵗ b)))
ife-sound Γ Γᵗ t e b W .(tceval Γᵗ t) .(tceval Γᵗ e)
  .(W + (tceval Γᵗ IF b THEN t ELSE e END + tbeval Γᵗ b))
  (TIF n1 .b .t .e .W) refl refl = refl

-- Now do loop here

-- Then do exec statement for 1 function call

-- Then exec statement for || and //

-- The evaluation time for all commands XXX: Not being used right now,
-- but maybe later I can change everything to a relation.
data _⇓_ : Cmd {ℕ} → ℕ → Set where
  NSKIP : SKIP ⇓ 0

  NASSIGN : ∀ (X : String) → (e : Aexp {ℕ})
            → (n : ℕ)
            → (Var X := e) ⇓ n

  NSEQ : ∀ (n1 n2 : ℕ) → (c1 c2 : Cmd {ℕ})
         → (c1 ⇓ n1) → (c2 ⇓ n2)
         → (c2 ¿ c2) ⇓ (n1 + n2)

  NIFT : (st : (String → ℕ)) → ∀ (n1 : ℕ) → (b : Bexp {ℕ}) →
        (t e : Cmd {ℕ}) → ∀ (W : ℕ)
        → beval st b ≡ true
        → t ⇓ n1
        → (IF b THEN t ELSE e END) ⇓ n1

  NIFE : (st : (String → ℕ)) → ∀ (n1 : ℕ) → (b : Bexp {ℕ}) →
        (t e : Cmd {ℕ}) → ∀ (W : ℕ)
        → beval st b ≡ false
        → e ⇓ n1
        → (IF b THEN t ELSE e END) ⇓ n1
