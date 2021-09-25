{-# OPTIONS --safe -W ignore #-}

module Map where

open import Data.String
open import Data.String.Properties using (_==_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)
import Relation.Nullary.Decidable.Core
import Data.List.Relation.Binary.Pointwise
import Data.List.Relation.Binary.Pointwise.Properties
import Agda.Builtin.Char.Properties
import Agda.Builtin.Char
import Data.Nat.Properties

-- The empty map
K : {A : Set} → (v : A) → (String → A)
K v = (λ _ → v)

-- Storing in map "m" with value "v" into key "k"
Store : {A : Set} → (m : (String → A)) → (k : String)
        → (v : A) → (String → A)
Store m k v = λ k' → if (k' == k) then v else m k'

-- Unit tests
open import Data.Nat

-- Example of initialising the variable stack
S : (String → ℕ)
S = K 0

-- Example of adding values to a stack
S1 : (String → ℕ)
S1 = Store S "a" 10

-- Adding the second variable
S2 : (String → ℕ)
S2 = Store S1 "b" 11

-- Getting the value of a from stack S2
A : ℕ
A = S2 "a"

-- Getting the value of b from stack S2
B : ℕ
B = S2 "b"

-- Try to get a string that is not in stack, gives the default value
C : ℕ
C = S2 "c"

-- Important properties

-- Lemma needed to prove the side condition between stacks after
-- function call
lemma-stack-eq : {A : Set} → ∀ (stm stf : (String → A)) → (X Y : String)
                 → (Store stm Y (stf X)) Y ≡ (stf X)
lemma-stack-eq stm stf X Y with (Y Data.String.≟ Y)
... | .true Relation.Nullary.because Relation.Nullary.ofʸ p = refl
... | .false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = ⊥-elim (¬p refl)

-- Now a very important property for proving the constancy rule
t-update-neq : {A : Set} → ∀ (st : (String → A)) → (x1 x2 : String)
               → (v : A) → ((x2 ≡ x1) → ⊥) → (Store st x1 v) x2 ≡ (st x2)
t-update-neq st x1 x2 v p with (Relation.Nullary.Decidable.Core.map′
        (λ x →
           Data.String.Properties.toList-injective x2 x1
           (Data.List.Relation.Binary.Pointwise.Pointwise-≡⇒≡ x))
        (λ x →
           Data.List.Relation.Binary.Pointwise.≡⇒Pointwise-≡ (cong toList x))
        (Data.List.Relation.Binary.Pointwise.Properties.decidable
         (λ x y →
            Relation.Nullary.Decidable.Core.map′
            (Agda.Builtin.Char.Properties.primCharToNatInjective x y)
            (cong Agda.Builtin.Char.primCharToNat)
            (Relation.Nullary.Decidable.Core.map′
             (Data.Nat.Properties.≡ᵇ⇒≡ (Agda.Builtin.Char.primCharToNat x)
              (Agda.Builtin.Char.primCharToNat y))
             (Data.Nat.Properties.≡⇒≡ᵇ (Agda.Builtin.Char.primCharToNat x)
              (Agda.Builtin.Char.primCharToNat y))
             (T?
              (Agda.Builtin.Char.primCharToNat x ≡ᵇ
               Agda.Builtin.Char.primCharToNat y))))
         (toList x2) (toList x1)))
... | false Relation.Nullary.because Relation.Nullary.ofⁿ ¬p = refl
... | true Relation.Nullary.because Relation.Nullary.ofʸ refl = ⊥-elim (p refl)

-- Testing lookup with nested stores
test : {A : Set} →  ∀ (x1 x2 y : String) → (st st' : (String → A))
       → (v1 v2 : A) → (y ≡ x1 → ⊥) → (y ≡ x2 → ⊥)
       → (st' ≡ (Store (Store st x1 v1) x2 v2))
       → st' y ≡ st y
test x1 x2 y st st' v1 v2 p1 p2 q rewrite q 
  | t-update-neq (Store st x1 v1) x2 y v2 p2
  | t-update-neq st x1 y v1 p1 = refl


-- Partial map
open import Data.Maybe

KP : {A : Set} → (String → Maybe A)
KP = (λ _ → nothing)

StoreP : {A : Set} → (st : (String → Maybe A))
         → (x : String) → (v : A)
         → (String → Maybe A)
StoreP st x v = λ x' → if x == x' then just v else st x'
