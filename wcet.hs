--XXX: Change 1 to whatever value you want depending upon the number of
-- clock cycles the operation takes.

module Wcet where

import Control.Parallel(par, pseq)

data Aexp =
  Plus Aexp Aexp
  | Minus Aexp Aexp
  | Mult Aexp Aexp
  | Avar String
  | Anum Int
  deriving (Show)

data Bexp =
  TRUE
  | FALSE
  | And Bexp Bexp
  | Or Bexp Bexp
  | Lth Aexp Aexp
  | Gth Aexp Aexp
  | LEQ Aexp Aexp
  | GEQ Aexp Aexp
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
  --XXX: The last two Ints are fork time and join time
  | PAR FuncCall FuncCall
  deriving (Show)

-- Computing the wcet for the function call
wcet_func :: FuncCall -> Int
wcet_func (FCall _ a s r) = store * (numars a) + store * (numars r)
                            + compute_wcet s
  where
    --XXX: The number of clock cycles needed to copy each arg and ret
    --across stacks.
    store = 1
wcet_func (PAR f1 f2) = ft1 `par` (ft2 `pseq` (ft1 + ft2)) + ft + jt
  where
    ft1 = wcet_func f1
    ft2 = wcet_func f2
    --XXX: These are the number of clock cycles for fork and join
    ft = 1
    jt = 1


data Statements =
  Skip
  | Assign String Aexp
  | Seq Statements Statements
  | Ite Bexp Statements Statements
  | LOOP Bexp Statements Int -- Here Int is the max loop count
  | Exec FuncCall
  deriving (Show)

-- wcet aexp
wcet_aexp :: Aexp -> Int
wcet_aexp (Plus l r) = wcet_aexp l + wcet_aexp r + 1
wcet_aexp (Minus l r) = wcet_aexp l + wcet_aexp r + 1
wcet_aexp (Mult l r) = wcet_aexp l + wcet_aexp r + 1
wcet_aexp (Avar _) = 1
wcet_aexp (Anum _) = 1

wcet_bexp :: Bexp -> Int
wcet_bexp TRUE = 1
wcet_bexp FALSE = 1
wcet_bexp (And l r) = wcet_bexp l + wcet_bexp r + 1
wcet_bexp (Or l r) = wcet_bexp l + wcet_bexp r + 1
wcet_bexp (Lth l r) = wcet_aexp l + wcet_aexp r + 1
wcet_bexp (Gth l r) = wcet_aexp l + wcet_aexp r + 1
wcet_bexp (LEQ l r) = wcet_aexp l + wcet_aexp r + 1
wcet_bexp (GEQ l r) = wcet_aexp l + wcet_aexp r + 1
wcet_bexp (Not r) = wcet_bexp r + 1


-- This gives the total WCET using Hoare rules
compute_wcet :: Statements -> Int
compute_wcet Skip = 0
compute_wcet (Assign _ e) = wcet_aexp e + 1
compute_wcet (Seq l r) = lw `par` (rw `pseq` (lw + rw)) 
  where
    lw = compute_wcet l
    rw = compute_wcet r
compute_wcet (Ite b t e) = wcet_bexp b + lt `par` (et `pseq` lt + et)
  where
    lt = compute_wcet t
    et = compute_wcet e
compute_wcet (LOOP b c w) = ct + (wcet_bexp b) * (w + 1)
  where
    ct = (compute_wcet c) * w
--XXX: This is the not the same as compositional Hoare, because I am
--computing the WCET here from the commands inside func
compute_wcet (Exec func) = wcet_func func

-- XXX: Example program
program :: Statements
program = Assign "X" (Anum 10)
          `Seq`
          Assign "X" (Plus (Avar "X") (Anum 1))
          `Seq`
          Ite (Lth (Avar "X") (Anum 10))
          (Assign "X" (Plus (Anum 2) (Avar "X")))
          (Assign "X" (Minus (Avar "X") (Anum 2)))
          `Seq`
          Skip

-- This is the main function
main :: IO ()
main = do
  let wcet = compute_wcet program in
    putStrLn $ show wcet
  putStrLn $ show program
