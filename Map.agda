{-# OPTIONS --safe #-}

module Map where

open import Data.String
open import Data.String.Properties using (_==_)
open import Data.Bool

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

-- Partial map
open import Data.Maybe

KP : {A : Set} → (String → Maybe A)
KP = (λ _ → nothing)

StoreP : {A : Set} → (st : (String → Maybe A))
         → (x : String) → (v : A)
         → (String → Maybe A)
StoreP st x v = λ x' → if x == x' then just v else st x'
