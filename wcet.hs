-- -*- mode: haskell; flycheck-checker: haskell-ghc; -*-


--XXX: Change 1 to whatever value you want depending upon the number of
-- clock cycles the operation takes.

module Wcet where

import Control.Parallel(par, pseq)

data Aexp =
  Plus Aexp Aexp
  | Minus Aexp Aexp
  | Mult Aexp Aexp
  | Div Aexp Aexp
  | Avar String
  | Anum Int
  deriving (Show)

data Bexp =
  TRUE
  | FALSE
  | And Bexp Bexp
  | Or Bexp Bexp
  | Lt Aexp Aexp
  | Eq Aexp Aexp
  | Gt Aexp Aexp
  | Leq Aexp Aexp
  | Geq Aexp Aexp
  | Not Bexp
  deriving (Show)

data ARs =
  R String
  | RComma ARs ARs
  deriving (Show)

numars :: ARs -> Int
numars (R _) = 1
numars (RComma l r) = numars l + numars r

data FuncCall =
  FCall String ARs Statements ARs
  | PAR FuncCall FuncCall
  deriving (Show)

-- Computing the wcet for the function call
wcetFunc :: FuncCall -> Int
wcetFunc (FCall _ a s r) = store * numars a + store * numars r
                            + computeWcet s
  where
    --XXX: The number of clock cycles needed to copy each arg and ret
    --across stacks.
    store = 1
wcetFunc (PAR f1 f2) = ft1 `par` (ft2 `pseq` (ft1 `max` ft2)) + ft + jt
  where
    ft1 = wcetFunc f1
    ft2 = wcetFunc f2
    --XXX: These are the number of clock cycles for fork and join
    ft = 1
    jt = 1

data Statements =
  Skip
  | Assign String Aexp
  | Seq Statements Statements
  | Ite Bexp Statements Statements
  | Loop Bexp Statements Int -- Here Int is the max loop count
  | Exec FuncCall
  deriving (Show)

-- wcet aexp
wcetAexp :: Aexp -> Int
wcetAexp (Plus l r) = wcetAexp l + wcetAexp r + 1
wcetAexp (Minus l r) = wcetAexp l + wcetAexp r + 1
wcetAexp (Mult l r) = wcetAexp l + wcetAexp r + 1
wcetAexp (Div l r) = wcetAexp l + wcetAexp r + 1
wcetAexp (Avar _) = 1
wcetAexp (Anum _) = 1

wcetBexp :: Bexp -> Int
wcetBexp TRUE = 1
wcetBexp FALSE = 1
wcetBexp (And l r) = wcetBexp l + wcetBexp r + 1
wcetBexp (Or l r) = wcetBexp l + wcetBexp r + 1
wcetBexp (Lt l r) = wcetAexp l + wcetAexp r + 1
wcetBexp (Gt l r) = wcetAexp l + wcetAexp r + 1
wcetBexp (Leq l r) = wcetAexp l + wcetAexp r + 1
wcetBexp (Eq l r) = wcetAexp l + wcetAexp r + 1
wcetBexp (Geq l r) = wcetAexp l + wcetAexp r + 1
wcetBexp (Not r) = wcetBexp r + 1

-- This gives the total WCET using Hoare rules
computeWcet :: Statements -> Int
computeWcet Skip = 0
computeWcet (Assign _ e) = wcetAexp e + store
  where
    store = 1
computeWcet (Seq l r) = lw `par` (rw `pseq` (lw + rw)) 
  where
    lw = computeWcet l
    rw = computeWcet r
computeWcet (Ite b t e) = wcetBexp b + lt `par` (et `pseq` lt `max` et)
  where
    lt = computeWcet t
    et = computeWcet e
computeWcet (Loop b c w) = ct + wcetBexp b * (w + 1)
  where
    ct = computeWcet c * w
--XXX: This is the not the same as compositional Hoare, because I am
--computing the WCET here from the commands inside func
computeWcet (Exec func) = wcetFunc func

-- XXX: Example program showing that nested loops should account for
-- number of iterations correctly -- should give the same result at the
-- original IPET WCET
ipet_ex1_claire :: Statements
ipet_ex1_claire =
  Assign "i" (Anum 0)
  `Seq`
  Assign "j" (Anum 0)
  `Seq`
  Assign "X" (Anum 0)
  `Seq`
  Loop (Lt (Avar "i") (Anum 4))
  (
    Assign "X" (Anum 1)
    `Seq`
    Loop (Lt (Avar "j") (Anum 5))
    (
      Assign "X" (Plus (Avar "i") (Avar "j"))
      `Seq`
      Assign "j" (Plus (Avar "j") (Anum 1))
    ) 5
    `Seq`
    Assign "j" (Plus (Avar "i") (Anum 1))
  ) 4

--XXX: Second example showing that explicit paths can be considered
--correctly via the rules -- should give the same result at the orignal
--IPET method for WCET analysis.
nestedIf :: Statements
nestedIf =
  Assign "X" (Anum 1)
  `Seq`
  Assign "Y" (Anum 1)
  `Seq`
  Assign "Z" (Anum 1)
  `Seq`
  Ite (Lt (Avar "X") (Anum 1))
  (Ite (Gt (Avar "Y") (Anum 4))
  ( -- Then branch of inner if
    Assign "Z" (Anum 1)
    `Seq`
    Assign "Z" (Plus (Anum 1) (Anum 6))
  )
  ( -- Else branch of inner if
    Assign "Z" (Anum 4)
  ))
  ( --Else branch of outter if
    Assign "Z" (Plus (Avar "X") (Anum 1))
  )

--XXX: We are not cutting out infeasible paths, so the WCET can be a
--large over-estimate. XXX: Another example from Tulika' paper
tulikaIte :: Statements
tulikaIte =
  Ite (Gt (Avar "x") (Anum 3))
   (Assign "z" (Plus (Avar "z") (Anum 1)))
   (Assign "x" (Anum 1))
  `Seq`
  Ite (Eq (Avar "y") (Anum 4))
   (Assign "y" (Plus (Avar "y") (Anum 1)))
   (Assign "x" (Anum 1)) 
  `Seq`
  Ite (Lt (Avar "x") (Anum 2))
   (Assign "z" (Div (Avar "z") (Anum 2)))
   (Assign "z" (Minus (Avar "z") (Anum 1)))


  
-- This is the main function
main :: IO ()
main = do
  let wcet1 = computeWcet ipet_ex1_claire in
    print wcet1
  let wcet2 = computeWcet nestedIf in
    print wcet2
  let wcet3 = computeWcet tulikaIte in
    print wcet3
