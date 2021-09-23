-- {-# OPTIONS --safe #-}
module Language where

open import Map
open import Relation.Binary.PropositionalEquality
open import Data.String using (String)
open import Data.Nat
open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)

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

-- Example of a program with multiple functions
Main : Top
Main = DEF "Factorial" < Arg "K" >⇒< Ret "fact" ,` Ret "K" >:
            Var "n" := Avar "K" ¿
            Var "fact" := Anum 1 ¿
            WHILE (Avar "n" >` Anum 0) DO
              Var "fact" := Avar "fact" *` Avar "n" ¿
              Var "n" := Avar "n" -` Anum 1
            END ¿
            Var "res" := Anum 0 ¿
            IF ((Avar "K" ≡` Anum 4) &&` (Avar "fact" ≡` Anum 24)) THEN
              Var "res" := Anum 1
            ELSE
              Var "res" := Anum 0
            END
       END ¿
       MAIN:
        Var "K" := Anum 4 ¿
        -- The below 2 have to be declared before being used
        Var "fact" := Anum 0 ¿
        -- We should also have a tuple with each function/thread for
        -- pre-post.
        EXEC < Ret "fact" ,` Ret "K" >:= "Factorial" < Arg "K" >
       END


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

-- Semantics from here


-- All stacks should come from point of function call
-- Here Γ is the caller' stack
data _,_-[_]->ᴬ_ {A : Set} (Γ : (String → ( A))) :
                (String → ( A)) → (ATuple)
                → (String →  A) → Set where
  hd : ∀ (v : String) → ∀ (st : (String →  A)) →
         -- Γ v ≡ just vv →  -- Make sure that Arg is in the caller' stack
         -----------------------------------------------------------
         Γ , st -[ Arg v ]->ᴬ (Store st v (Γ v))

  tl : (l r : ATuple) → (st st' st'' : (String →  A)) →
        (Γ , st -[ l ]->ᴬ st') → (Γ , st' -[ r ]->ᴬ st'') →
        -----------------------------------------------------------
        Γ , st -[ (l ,` r) ]->ᴬ st''

-- Here Γ is the callee' stack
data _,_-[_]->ᴿ_ {A : Set}
                 (Γ : (String →  A))  :
                 (String →  A) → RTuple → (String →  A)
                 → Set where
  hd : ∀ (v : String) → ∀ (v1 v2 : A) → ∀ (st : (String →  A)) →
       -- → Γ v ≡ just v1 → st v ≡ just v2 →
       -- (_⊕_ : A → A → A) → ∀ (a b c : A) → (a ⊕ b ≡ b ⊕ a)
       -- → ((a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)) →
       -----------------------------------------------------------
       Γ , st -[ Ret v  ]->ᴿ (Store st v (Γ v))
       -- Γ , st -[ Ret v  ]->ᴿ (Store st v (Γ v ⊕ st v))

  tl : ∀ (l r : RTuple) → (st st' st'' : (String →  A)) →
       (Γ , st -[ l ]->ᴿ st') → (Γ , st' -[ r ]->ᴿ st'') →
       -----------------------------------------------------------
       Γ , st -[ (l ,` r) ]->ᴿ st''


mutual

-- These are the relations for ℕ
 data _,_=[_]=>_ (Γ : String → Maybe (ProgTuple {ℕ})) :
                 (String →  ℕ) →
                 Cmd {ℕ} → (String →  ℕ) →
                 Set where
  CSKIP : ∀ (st : (String →  ℕ)) →
          -----------------------
          Γ , st =[ SKIP ]=> st

  CASSIGN : ∀ (st : (String →  ℕ)) → ∀ (x : String) →
            ∀ (e : Aexp {ℕ}) →
          -----------------------------------------------------------
          Γ , st =[ Var x := e ]=> (Store st x (aeval st e))

  CSEQ : ∀ (st st' st'' : (String →  ℕ)) → ∀ (c1 c2 : Cmd {ℕ}) →
         Γ , st =[ c1 ]=> st' →
         Γ , st' =[ c2 ]=> st'' →
         -----------------------------------------------------------
         Γ , st =[ (c1 ¿ c2)]=> st''

  CIFT : ∀ (st st' : (String →  ℕ)) → (b : Bexp {ℕ}) →
         (t e : Cmd {ℕ}) →
         beval st b ≡ true →
         Γ , st =[ t ]=> st' →
         -----------------------------------------------------------
         Γ , st =[ (IF b THEN t ELSE e END)]=> st'

  CIFE : ∀ (st st' : (String →  ℕ)) →
         (b : Bexp {ℕ}) → (t e : Cmd {ℕ}) →
         beval st b ≡ false →
         Γ , st =[ e ]=> st' →
         -----------------------------------------------------------
         Γ , st =[ (IF b THEN t ELSE e END)]=> st'

  CLF : (st : (String →  ℕ)) →
        (b : Bexp {ℕ}) → (c : Cmd {ℕ}) →
         beval st b ≡ false →
         -----------------------------------------------------------
         Γ , st =[ (WHILE b DO c END) ]=> st

  CLT :  (st st' st'' : (String →  ℕ)) →
         (b : Bexp {ℕ}) → (c : Cmd {ℕ}) →
         beval st b ≡ true →
         Γ , st =[ c ]=> st' →
         Γ , st' =[ (WHILE b DO c END) ]=> st'' →
         -----------------------------------------------------------
         Γ , st =[ (WHILE b DO c END) ]=> st''

  -- XXX: Done.
  CEX : ∀ (f : FuncCall {ℕ}) → ∀ (st st' : (String → ℕ))
        → Γ , st =[ f ]=>ᶠ st'
        -----------------------------------------------------------
        → Γ , st =[ EXEC f ]=> st'
         
-- TODO: The function calls and definition with ℕ
 data _,_=[_]=>ᶠ_ (Γ : String → (Maybe (ProgTuple {ℕ}))) :
                (String → ℕ) → FuncCall {ℕ} → (String → ℕ)
                → Set where

  Base : ∀ (fname : String) →        -- name of the function
         ∀ (stm : String → ℕ) -- caller stack,
         → (stf' stf'' : String → ℕ) -- These are the pre-call and
                                     -- post-call callee stack,
                                     -- respectively.
         → (stm' : String → ℕ)       -- The resultant caller stack

         -- res of putting values on callee stack
         → stm , (K 0) -[ getProgArgs (Γ fname) ]->ᴬ stf' 

         -- result of running the function 
         → Γ , stf' =[ getProgCmd (Γ fname) ]=> stf'' 

         -- copying ret values back on caller' stack
         → stf'' , stm -[ getProgRets (Γ fname) ]->ᴿ stm' 

         -----------------------------------------------------------
         → Γ , stm =[ < getProgRets (Γ fname) >:=
             fname < getProgArgs (Γ fname) > ]=>ᶠ stm'

-- Doing the evaluation of top
evalProg : {A : Set} → (p : Top {A}) →
           (st : String → Maybe (ProgTuple {A})) →
           (String → Maybe (ProgTuple {A}))
evalProg MAIN: c END st = (StoreP st "MAIN" (Arg "void" , Ret "void" , c))
evalProg (DEF f < x >⇒< x1 >: c END ¿ p) st =
              StoreP (evalProg p st) f (x , x1 , c)

-- Example of relation on ℕ
ex1 : ∀ (Γ : (String → Maybe ProgTuple)) → ∀ (st : (String →  ℕ))
      → Γ , st =[ SKIP ]=> st
ex1 Γ st = CSKIP st



-- Hoare logic starts here!
{-# NO_POSITIVITY_CHECK #-}

-- XXX: Maybe later define another language for it?
-- Logical expressions with ℕ as relations (used for Hoare Propositions)
data _|=_ (st : String →  ℕ) : Bexp {ℕ} → Set where
  LT : ∀ (l r : Aexp {ℕ}) → (aeval st l) Data.Nat.< (aeval st r)
       → st |= (l <` r)
  LE : ∀ (l r : Aexp {ℕ}) → (aeval st l) Data.Nat.≤ (aeval st r)
       → st |= (l ≤` r)
  GT : ∀ (l r : Aexp {ℕ}) → (aeval st l) Data.Nat.> (aeval st r)
       → st |= (l >` r)
  GE : ∀ (l r : Aexp {ℕ}) → (aeval st l) Data.Nat.≥ (aeval st r)
       → st |= (l ≥` r)
  EQ : ∀ (l r : Aexp {ℕ}) → (aeval st l) ≡ (aeval st r)
       → st |= (l ≡` r)
  TT : st |= TRUE
  AND : ∀ (b1 b2 : Bexp {ℕ}) → (st |= b1) → (st |= b2)
        → st |= (b1 &&` b2)
  ORL : ∀ (b1 b2 : Bexp {ℕ}) → (st |= b1) → (st |= (b1 ||` b2))
  ORR : ∀ (b1 b2 : Bexp {ℕ}) → (st |= b2) → (st |= (b1 ||` b2))
  -- XXX: Had to disable POSITIVITY_CHECK
  NOT : ∀ (b : Bexp {ℕ}) → ((st |= b) → ⊥) → st |= (¬` b)

-- Assert with ℙrops
Assertℙ : ∀ (b : Bexp {ℕ}) → (String → ℕ) → Set
Assertℙ b st = st |= b

-- Defn of substitution rule with ℙrop
Subsℙ : ∀ (b : Bexp {ℕ})       -- b is my assertion
       → (X : String)
       → (e : Aexp {ℕ}) → (String → ℕ)
       → Set
Subsℙ b X e st = (Store st X (aeval st e)) |= b

getStates : ∀ (stf stm : String → ℕ) → ATuple → (String → ℕ)
getStates stf stm (Arg v) = Store stf v (stm v)
getStates stf stm (l ,` r) = getStates (getStates stf stm l) stm r

getStatesR : ∀ (stm stf : String → ℕ) → RTuple → (String → ℕ)
getStatesR stm stf (Ret v) = Store stm v (stf v)
getStatesR stm stf (rets ,` rets₁) = getStatesR (getStatesR stm stf rets) stf rets₁

-- Subs for the input arguments before calling a function
SubsArgs : ∀ (Q : Bexp {ℕ}) → (args : ATuple) → (stf stm : (String → ℕ))
           → Set
SubsArgs Q args stf stm = (getStates stf stm args) |= Q

-- Subs for the output rets after calling function
SubsRets : ∀ (R : Bexp {ℕ}) → (rets : RTuple) → (stm stf : (String → ℕ))
           → Set
SubsRets R rets stm stf = (getStatesR stm stf rets) |= R

-- Lemma for getStates
getstates-eq-lemma : ∀ (st stm st' : (String → ℕ)) → (args : ATuple)
                     → stm , st -[ args ]->ᴬ st'
                     → (getStates st stm args) ≡ st'
getstates-eq-lemma st stm .(Store st v (stm v)) (Arg v) (hd .v .st) = refl
getstates-eq-lemma st stm st' (args ,` args₁) (tl .args .args₁ .st st'' .st' cmd cmd₁) with getstates-eq-lemma st stm st'' args cmd
... | refl = getstates-eq-lemma st'' stm st' args₁ cmd₁

-- Lemma for getStatesR
getstatesr-eq-lemma : ∀ (stm stf stm' : (String → ℕ)) → (rets : RTuple)
                      → (stf , stm -[ rets ]->ᴿ stm')
                      → (getStatesR stm stf rets) ≡ stm'
getstatesr-eq-lemma stm stf .(Store stm v (stf v)) .(Ret v) (hd v v1 v2 .stm) = refl
getstatesr-eq-lemma stm stf stm' .(l ,` r) (tl l r .stm st' .stm' cmd cmd₁) with getstatesr-eq-lemma stm stf st' l cmd
... | refl = getstatesr-eq-lemma st' stf stm' r cmd₁

-- Now the soundness proof for SubsArgs
SubsArgs-theorem : ∀ (stf stm stf' : (String → ℕ)) → (Q : Bexp {ℕ})
                   → (args : ATuple) → (P : SubsArgs Q args stf stm)
                   → (cmd : stm , stf -[ args ]->ᴬ stf')
                   → (stf' |= Q)
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(l <` r) .(Arg v) (LT l r x) (hd v .stf) = LT l r x
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(l ≤` r) .(Arg v) (LE l r x) (hd v .stf) = LE l r x
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(l >` r) .(Arg v) (GT l r x) (hd v .stf) = GT l r x
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(l ≥` r) .(Arg v) (GE l r x) (hd v .stf) = GE l r x
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(l ≡` r) .(Arg v) (EQ l r x) (hd v .stf) = EQ l r x
SubsArgs-theorem stf stm .(Store stf v (stm v)) .TRUE .(Arg v) TT (hd v .stf) = TT
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(b1 &&` b2) .(Arg v) (AND b1 b2 P P₁) (hd v .stf) = AND b1 b2 P P₁
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(b1 ||` b2) .(Arg v) (ORL b1 b2 P) (hd v .stf) = ORL b1 b2 P
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(b1 ||` b2) .(Arg v) (ORR b1 b2 P) (hd v .stf) = ORR b1 b2 P
SubsArgs-theorem stf stm .(Store stf v (stm v)) .(¬` b) .(Arg v) (NOT b x) (hd v .stf) = NOT b x
SubsArgs-theorem stf stm stf' .(l₁ <` r₁) .(l ,` r) (LT l₁ r₁ x) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = LT l₁ r₁ x
SubsArgs-theorem stf stm stf' .(l₁ ≤` r₁) .(l ,` r) (LE l₁ r₁ x) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = LE l₁ r₁ x 
SubsArgs-theorem stf stm stf' .(l₁ >` r₁) .(l ,` r) (GT l₁ r₁ x) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = GT l₁ r₁ x
SubsArgs-theorem stf stm stf' .(l₁ ≥` r₁) .(l ,` r) (GE l₁ r₁ x) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = GE l₁ r₁ x
SubsArgs-theorem stf stm stf' .(l₁ ≡` r₁) .(l ,` r) (EQ l₁ r₁ x) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = EQ l₁ r₁ x
SubsArgs-theorem stf stm stf' .TRUE .(l ,` r) TT (tl l r .stf st' .stf' cmd cmd₁) = TT
SubsArgs-theorem stf stm stf' .(b1 &&` b2) .(l ,` r) (AND b1 b2 P P₁) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = AND b1 b2 P P₁
SubsArgs-theorem stf stm stf' .(b1 ||` b2) .(l ,` r) (ORL b1 b2 P) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = ORL b1 b2 P
SubsArgs-theorem stf stm stf' .(b1 ||` b2) .(l ,` r) (ORR b1 b2 P) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = ORR b1 b2 P
SubsArgs-theorem stf stm stf' .(¬` b) .(l ,` r) (NOT b x) (tl l r .stf st' .stf' cmd cmd₁) rewrite getstates-eq-lemma stf stm st' l cmd | getstates-eq-lemma st' stm stf' r cmd₁ = NOT b x

-- DONE: We can do the same as above for ret but with stacks swapped
SubsRets-theorem : ∀ (stm stf stm' : (String → ℕ)) → (Q : Bexp {ℕ})
                   → (rets : RTuple) → (P : SubsRets Q rets stm stf)
                   → (cmd : stf , stm -[ rets ]->ᴿ stm')
                   → (stm' |= Q)
SubsRets-theorem stm stf .(Store stm v (stf v)) .(l <` r) .(Ret v) (LT l r x) (hd v v1 v2 .stm) = LT l r x
SubsRets-theorem stm stf .(Store stm v (stf v)) .(l ≤` r) .(Ret v) (LE l r x) (hd v v1 v2 .stm) = LE l r x
SubsRets-theorem stm stf .(Store stm v (stf v)) .(l >` r) .(Ret v) (GT l r x) (hd v v1 v2 .stm) = GT l r x
SubsRets-theorem stm stf .(Store stm v (stf v)) .(l ≥` r) .(Ret v) (GE l r x) (hd v v1 v2 .stm) = GE l r x
SubsRets-theorem stm stf .(Store stm v (stf v)) .(l ≡` r) .(Ret v) (EQ l r x) (hd v v1 v2 .stm) = EQ l r x
SubsRets-theorem stm stf .(Store stm v (stf v)) .TRUE .(Ret v) TT (hd v v1 v2 .stm) = TT
SubsRets-theorem stm stf .(Store stm v (stf v)) .(b1 &&` b2) .(Ret v) (AND b1 b2 P P₁) (hd v v1 v2 .stm) = AND b1 b2 P P₁
SubsRets-theorem stm stf .(Store stm v (stf v)) .(b1 ||` b2) .(Ret v) (ORL b1 b2 P) (hd v v1 v2 .stm) = ORL b1 b2 P
SubsRets-theorem stm stf .(Store stm v (stf v)) .(b1 ||` b2) .(Ret v) (ORR b1 b2 P) (hd v v1 v2 .stm) = ORR b1 b2 P
SubsRets-theorem stm stf .(Store stm v (stf v)) .(¬` b) .(Ret v) (NOT b x) (hd v v1 v2 .stm) = NOT b x
SubsRets-theorem stm stf stm' .(l₁ <` r₁) .(l ,` r) (LT l₁ r₁ x) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = LT l₁ r₁ x
SubsRets-theorem stm stf stm' .(l₁ ≤` r₁) .(l ,` r) (LE l₁ r₁ x) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = LE l₁ r₁ x
SubsRets-theorem stm stf stm' .(l₁ >` r₁) .(l ,` r) (GT l₁ r₁ x) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = GT l₁ r₁ x
SubsRets-theorem stm stf stm' .(l₁ ≥` r₁) .(l ,` r) (GE l₁ r₁ x) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = GE l₁ r₁ x
SubsRets-theorem stm stf stm' .(l₁ ≡` r₁) .(l ,` r) (EQ l₁ r₁ x) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = EQ l₁ r₁ x
SubsRets-theorem stm stf stm' .TRUE .(l ,` r) TT (tl l r .stm st' .stm' cmd cmd₁) = TT
SubsRets-theorem stm stf stm' .(b1 &&` b2) .(l ,` r) (AND b1 b2 P P₁) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = AND b1 b2 P P₁
SubsRets-theorem stm stf stm' .(b1 ||` b2) .(l ,` r) (ORL b1 b2 P) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = ORL b1 b2 P
SubsRets-theorem stm stf stm' .(b1 ||` b2) .(l ,` r) (ORR b1 b2 P) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = ORR b1 b2 P
SubsRets-theorem stm stf stm' .(¬` b) .(l ,` r) (NOT b x) (tl l r .stm st' .stm' cmd cmd₁) rewrite getstatesr-eq-lemma stm stf st' l cmd | getstatesr-eq-lemma st' stf stm' r cmd₁ = NOT b x

-- Lemma needed to prove the side condition between stacks after
-- function call
lemma-stack-eq : ∀ (stm stf : (String → ℕ)) → (X Y : String)
                 → (Store stm Y (stf X)) Y ≡ (stf X)
lemma-stack-eq stm stf X Y with (Y Data.String.≟ Y)
... | .true Relation.Nullary.because Relation.Nullary.ofʸ p = refl
... | .false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = ⊥-elim (¬p refl)

-- XXX: Use the above lemma to show the side condition state of R' X ≡
-- stf I and so on for all outputs.

-- Subs theorem states that Hoare' subs rule is valid (or sound)
subs-theoremℙ : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
          → ∀ (st st' : (String → ℕ)) → (X : String) → (e : Aexp {ℕ})
          → (Q : Bexp {ℕ}) → (P : (Subsℙ Q X e st))
          → (C : Γ , st =[ Var X := e ]=> st')
          → (Assertℙ Q st')
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(l <` r) (LT l r x) (CASSIGN .st .X .e) = LT l r x
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(l ≤` r) (LE l r x) (CASSIGN .st .X .e) = LE l r x
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(l >` r) (GT l r x) (CASSIGN .st .X .e) = GT l r x
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(l ≥` r) (GE l r x) (CASSIGN .st .X .e) = GE l r x
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(l ≡` r) (EQ l r x) (CASSIGN .st .X .e) = EQ l r x
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .TRUE TT (CASSIGN .st .X .e) = TT
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(b1 &&` b2) (AND b1 b2 p p₁) (CASSIGN .st .X .e) = AND b1 b2 p p₁
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(b1 ||` b2) (ORL b1 b2 p) (CASSIGN .st .X .e) = ORL b1 b2 p
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(b1 ||` b2) (ORR b1 b2 p) (CASSIGN .st .X .e) = ORR b1 b2 p
subs-theoremℙ Γ st .(Store st X (aeval st e)) X e .(¬` b) (NOT b p) (CASSIGN .st .X .e) = NOT b p


-- Consequence hoare rule theorem the general case soundness theorem.
-- This works for both P₁ ⇒ P ∧ Q ⇒ Q₁. Model the implication using (¬`
-- P₁) ||` P and (¬` Q) ||` Q₁
cons-theorem : ∀ (st : (String → ℕ)) → ∀ (P Q : Bexp {ℕ}) → Assertℙ P st
             → st |= ((¬` P) ||` Q) → Assertℙ Q st
cons-theorem st P Q a (ORL .(¬` P) .Q (NOT .P x)) = ⊥-elim (x a)
cons-theorem st P Q a (ORR .(¬` P) .Q b) = b

-- The SKIP Hoare rule soundness theorem
skip-theorem : ∀ (Γ : String → Maybe (ProgTuple {ℕ})) →
               ∀ (st st' : (String → ℕ)) → ∀ (P : Bexp {ℕ})
               → Assertℙ P st → Γ , st =[ SKIP ]=> st'
               → Assertℙ P st'
skip-theorem Γ st .st p sk (CSKIP .st) = sk

-- The Sequence Hoare rule soundness theorem.

-- Definition of a sound sequence rule
data _,≪_≫_≪_≫ (Γ : String → Maybe (ProgTuple {ℕ})) : Bexp {ℕ}
                  → Cmd {ℕ} → Bexp {ℕ} → Set where
  HSEQ : ∀ (st st' :  (String → ℕ))
         → (c1 c2 : Cmd {ℕ})
         → (P Q : Bexp {ℕ})
         → st |= P
         → Γ , st =[ c1 ¿ c2 ]=> st'
         → st' |= Q
         →
         -----------------------------------------------------------
         Γ ,≪ P ≫ (c1 ¿ c2) ≪ Q ≫


-- The sequence rule soundness theorem
-- this is a different way of looking at it
seq-theorem : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
              → ∀ (st st' st'' : (String → ℕ))
              → (c1 c2 : Cmd {ℕ})
              → (P Q R : Bexp {ℕ})
              → (Γ , st =[ c1 ]=> st')
              → (Γ , st' =[ c2 ]=> st'')
              → st |= P
              → st' |= Q
              → st'' |= R
              → Γ ,≪ P ≫ c1 ¿ c2 ≪ R ≫
seq-theorem Γ st st' st'' c1 c2 P Q R sc1 sc2 p _ r
  = HSEQ st st'' c1 c2 P R p (CSEQ st st' st'' c1 c2 sc1 sc2) r


-- Help lemma
contradiction-lemma : ∀ (b : Bexp {ℕ}) → ∀ (st : (String → ℕ))
                      → (beval st b ≡ true)
                      → (beval st b ≡ false) → ⊥
contradiction-lemma b st p rewrite p = λ ()

-- Deterministic lemma for argument passing
deterministic-ret-lemma : ∀ (stf stm stm' stm'' : (String → ℕ)) → (rets : RTuple)
                          → (stm , stf -[ rets ]->ᴿ stm') → (stm , stf   -[ rets ]->ᴿ stm'')
                          → (stm' ≡ stm'')
deterministic-ret-lemma stf stm .(Store stf v (stm v)) .(Store stf v (stm v)) .(Ret v) (hd v v1 v2 .stf) (hd .v v3 v4 .stf) = refl
deterministic-ret-lemma stf stm stm' stm'' .(l ,` r) (tl l r .stf st' .stm' p1 p3) (tl .l .r .stf st'' .stm'' p2 p4) with deterministic-ret-lemma stf stm st' st'' l p1 p2
... | refl with deterministic-ret-lemma st' stm stm' stm'' r p3 p4
... | refl = refl

-- Deterministic lemma for argument passing
deterministic-arg-lemma : ∀ (stm stf stf' stf'' : (String → ℕ)) → (args : ATuple)
                          → (stm , stf -[ args ]->ᴬ stf') → (stm , stf -[ args ]->ᴬ stf'')
                          → (stf' ≡ stf'')
deterministic-arg-lemma stm stf .(Store stf v (stm v)) .(Store stf v (stm v)) .(Arg v) (hd v .stf) (hd .v .stf) = refl
deterministic-arg-lemma stm stf stf' stf'' .(l ,` r) (tl l r .stf st' .stf' p1 p3) (tl .l .r .stf st'' .stf'' p2 p4) with deterministic-arg-lemma stm stf st' st'' l p1 p2
... | refl with deterministic-arg-lemma stm st' stf' stf'' r p3 p4
... | refl = refl

mutual
-- The deterministic execution for function calls
 deterministic-func-theorem : ∀ (Γ : (String → Maybe (ProgTuple {ℕ})))
                              → ∀ (stm stm1 stm2 : (String → ℕ))
                              → ∀ (f : FuncCall {ℕ} )
                              → Γ , stm =[ f ]=>ᶠ stm2
                              → Γ , stm =[ f ]=>ᶠ stm1
                              → stm2 ≡ stm1
 deterministic-func-theorem Γ stm stm1 stm2 .(< getProgRets (Γ fname) >:= fname < getProgArgs (Γ fname) >) (Base fname .stm stf' stf'' .stm2 x x₁ x₂) (Base .fname .stm stf''' stf'''' .stm1 x₃ x₄ x₅) with deterministic-arg-lemma stm (K 0) stf' stf''' (getProgArgs (Γ fname)) x x₃
 ... | refl with deterministic-exec-theorem Γ stf' stf'' stf'''' (getProgCmd (Γ fname)) x₁ x₄
 ... | refl with deterministic-ret-lemma stm stf'' stm1 stm2 (getProgRets (Γ fname)) x₅ x₂
 ... | refl = refl

-- Lemma for deterministic execution of commands
 deterministic-exec-theorem : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
                           → ∀ (st st' st'' : String → ℕ)
                           → ∀ (c : Cmd {ℕ})
                           → Γ , st =[ c ]=> st'
                           → Γ , st =[ c ]=> st''
                           → st' ≡ st''
 deterministic-exec-theorem Γ st .st .st .SKIP (CSKIP .st) (CSKIP .st) = refl
 deterministic-exec-theorem Γ st .(Store st x (aeval st e)) .(Store st x (aeval st e)) .(Var x := e) (CASSIGN .st x e) (CASSIGN .st .x .e) = refl
 deterministic-exec-theorem Γ st st' st'' .(c1 ¿ c2) (CSEQ .st st''' .st' c1 c2 e1 e3) (CSEQ .st st'''' .st'' .c1 .c2 e2 e4) with deterministic-exec-theorem Γ st st''' st'''' c1 e1 e2
 ... | refl  with deterministic-exec-theorem Γ st''' st'' st' c2 e4 e3
 ... | refl = refl
 deterministic-exec-theorem Γ st st' st'' .(IF b THEN t ELSE e END) (CIFT .st .st' b t e x e1) (CIFT .st .st'' .b .t .e x₁ e2) with deterministic-exec-theorem Γ st st'' st' t e2 e1
 ... | refl = refl
 deterministic-exec-theorem Γ st st' st'' .(IF b THEN t ELSE e END) (CIFT .st .st' b t e x e1) (CIFE .st .st'' .b .t .e x₁ e2) = ⊥-elim (contradiction-lemma b st x x₁)
 deterministic-exec-theorem Γ st st' st'' .(IF b THEN t ELSE e END) (CIFE .st .st' b t e x e1) (CIFT .st .st'' .b .t .e x₁ e2) = ⊥-elim (contradiction-lemma b st x₁ x)
 deterministic-exec-theorem Γ st st' st'' .(IF b THEN t ELSE e END) (CIFE .st .st' b t e x e1) (CIFE .st .st'' .b .t .e x₁ e2) with deterministic-exec-theorem Γ st st'' st' e e2 e1
 ... | refl = refl
 deterministic-exec-theorem Γ st .st .st .(WHILE b DO c END) (CLF .st b c x) (CLF .st .b .c x₁) = refl
 deterministic-exec-theorem Γ st .st st'' .(WHILE b DO c END) (CLF .st b c x) (CLT .st st' .st'' .b .c x₁ e2 e3) = ⊥-elim (contradiction-lemma b st x₁ x)
 deterministic-exec-theorem Γ st st' .st .(WHILE b DO c END) (CLT .st st''' .st' b c x e1 e3) (CLF .st .b .c x₁) = ⊥-elim (contradiction-lemma b st x x₁)
 deterministic-exec-theorem Γ st st' st'' .(WHILE b DO c END) (CLT .st st''' .st' b c x e1 e3) (CLT .st st'''' .st'' .b .c x₁ e2 e4) with deterministic-exec-theorem Γ st st'''' st''' c e2 e1
 ... | refl with deterministic-exec-theorem Γ st''' st'' st' (WHILE b DO c END) e4 e3
 ... | refl = refl
 deterministic-exec-theorem Γ st st' st'' (EXEC < ret >:= f < args >) (CEX .(< ret >:= f < args >) .st .st' x) (CEX .(< ret >:= f < args >) .st .st'' x₁) with deterministic-func-theorem Γ st  st' st'' < ret >:= f < args > x₁ x
 ... | refl = refl

-- Proving seq rule soundness via standard technique
seq-theorem1 : ∀ (Γ : String → Maybe (ProgTuple {ℕ}))
              → ∀ (st1 st2 st3 st4 : (String → ℕ))
              → (c1 c2 : Cmd {ℕ})
              → (P Q R : Bexp {ℕ})
              → (Γ , st1 =[ c1 ]=> st2)
              → (Γ , st2 =[ c2 ]=> st3)
              → st1 |= P
              → st2 |= Q
              → st3 |= R
              → Γ , st1 =[ c1 ¿ c2 ]=> st4
              → st4 |= R
seq-theorem1 Γ st1 st2 st3 st4 c1 c2 P Q R ec1 ec2 st1p st2q st3r (CSEQ .st1 st' .st4 .c1 .c2 ec12 ec13) with deterministic-exec-theorem Γ st1 st2 st' c1 ec1 ec12
... | refl with deterministic-exec-theorem Γ st2 st3 st4 c2 ec2 ec13
... | refl = st3r

-- TODO: Add If-else and while soundness rules if you want here

-- This is the derivable one (completely syntactic, not semantic)

-- In my case I will follow the same technique as SF, but instead of
-- taking propositions I will take the state and the boolean expression
-- for each proposition. This will make the syntactic derivation of
-- Hoare rules possible.
