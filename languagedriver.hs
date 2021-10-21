module LanguageDrive where

import Language (Cmd(..), Aexp(..), Bexp(..), mkassert, store, computeWcet)
import qualified Prelude
import Data.Set as Set

-- Make operators for the command language
(!) :: Cmd -> Cmd -> Cmd
l ! r = Seq l r 

(>) :: Aexp -> Aexp -> Bexp
l > r = Gt l r

(<) :: Aexp -> Aexp -> Bexp
l < r = Lt l r

(<=) :: Aexp -> Aexp -> Bexp
l <= r = Leq l r

(>=) :: Aexp -> Aexp -> Bexp
l >= r = Geq l r

(&&) :: Bexp -> Bexp -> Bexp
l && r = And l r

(||) :: Bexp -> Bexp -> Bexp
l || r = Or l r

(^) :: Bexp -> Bexp -> Bexp
l ^ r = Xor l r

(==) :: Aexp -> Aexp -> Bexp
l == r = Eq l r

(!=) :: Prelude.String -> Aexp -> Cmd
l != r = Assign l r

(*) :: Aexp -> Aexp -> Aexp
l * r = Mul l r

(/) :: Aexp -> Aexp -> Aexp
l / r = Div l r

(+) :: Aexp -> Aexp -> Aexp
l + r = Plus l r

(-) :: Aexp -> Aexp -> Aexp
l - r = Minus l r

-- Operator fixities
infix 5 !=
infixl 4 !
infixl 7 *
infixl 7 /
infixl 6 +
infixl 6 -

prog1 :: Cmd
prog1 =
  Seq (Seq (If (Eq (Avar "init") (Anum ((Prelude.+ 1) 0))) (Assign "m" (Plus
    (Avar "m") (Anum ((Prelude.+ 1) 0)))) (Assign "u" (Minus (Avar "u") (Anum
    ((Prelude.+ 1) 0))))) (If (Eq (Avar "Y") (Anum ((Prelude.+ 1) 0)))
    (Assign "cond" (Bexp0 (Not (Avar "init" == Anum ((Prelude.+ 1) 0)))))
    (Assign "cond" (Bexp0 True)))) (If (Eq (Avar "cond") (Bexp0 True))
    (Assign "m" (Avar "m" + Anum ((Prelude.+ 1) 0))) (Assign "u1"
    (Avar "u1" - Anum ((Prelude.+ 1) 0))))

prog2 :: Cmd
prog2 =
  Seq (Seq ("X" != Plus (Avar "Y") (Anum ((Prelude.+ 1) ((Prelude.+ 1)
    ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) 0))))))))
    ("X" != (Avar "Y" * Anum ((Prelude.+ 1) ((Prelude.+ 1)
    ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) 0)))))))))
    (Assign "X" (Avar "Y"))

--XXX: Program 1 Pascal Raymod' paper
prog3 :: Cmd
prog3 = If (Avar "init" == Anum 1)
        ("x" != Avar "x" * Anum 1 !
          "x" != Avar "x" * Anum 1!
          "x" != Avar "x" * Anum 1)
        ("y" != Anum 10) ! --E branch
        "i" != Anum 0 !
        While (Avar "i" < Avar "n")
        (If (Avar "Y" == Anum 1)
          ("cond" != Bexp0 (Not (Avar "init" == Anum 1))) --T branch
          ("cond" != Bexp0 True !                         --E branch
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1) !
         If (Avar "cond" == Bexp0 True)
          ("t" != Anum 9 * Anum 100) --T branch
          ("meme" != Anum 90 + Avar "r" ! --E branch
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1) !
          "i" != Avar "i" + Anum 1) 3 []

--XXX: Program 2: Pascal Raymond' paper
prog4 :: Cmd
prog4 = If (Avar "init" == Anum 1)
        ("x" != Avar "x" * Anum 1 !
          "x" != Avar "x" * Anum 1 !
          "x" != Avar "x" * Anum 1)
        ("y" != Anum 10) ! --E branch
        "i" != Anum 0 !
        While (Avar "i" < Avar "n")
        (If (Avar "cond" == Bexp0 True)
          ("t" != Anum 9 * Anum 100) --T branch
          ("meme" != Anum 90 + Avar "r" ! --E branch
           "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1) !
         If (Avar "Y" == Anum 1)
          ("cond" != Bexp0 (Not (Avar "init" == Anum 1))) --T branch
          ("cond" != Bexp0 True !
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1 !
            "x" != Avar "x" * Anum 1) !
          "i" != Avar "i" + Anum 1) 3 []
        
--XXX: Program 5 Pascal Raymond' paper
prog5 :: Cmd
prog5 = "i" != Anum 0!
        -- Assign cond some random number
        "cond" != Anum 1!
        While (Avar "i" < Anum 3)
        (If (Avar "cond" == Anum 1)
         ("x" != Avar "x" * Anum 1010!
          "cond" != Anum 0)
         ("cond" != Anum 1)) 3 []


--Example janne Complex
janneComplex :: Cmd
janneComplex =
  While (Avar "a" < Anum 30)
  (
    While(Avar "a" < Avar "b")
    (
      If (Avar "b" > Anum 5)
      ("b" != Avar "b" * Anum 3)
      ("b" != Avar "b" + Anum 2)!
      If ((Avar "b" >= Anum 10) && (Avar "b" <= Anum 12))
      ("a" != Avar "a" + Anum 10)
      ("a" != Avar "a" + Anum 1)
    ) 9 [] !
  "a" != Avar "a" + Anum 2!
  "b" != Avar "b" - Anum 10
  ) 11 []

sqrtFunction :: Cmd
sqrtFunction =
  "x" != Avar "val" * Anum 0.1!
  "dx" != Anum 0 !
  "diff" != Anum 0 !
  "min_tol" != Anum 0.00001!
  "i" != Anum 0!
  "flag" != Anum 0 !
  If (Avar "val" == Anum 0)
  ("x" != Anum 0)
  (
    "i" != Anum 1 !
    While(Avar "i" < Anum 20)
    (
      If(Avar "flag" == Anum 0)
      (
        "dx" != (Avar "val" - (Avar "x" * Avar "x")) / (Anum 2 * Avar "x") !
        "x" != Avar "x" + Avar "dx" !
        "diff" != Avar "val" - (Avar "x" * Avar "x") !
        If(Avar "diff" <= Avar "min_tol")
        ("flag" != Anum 1) Skip
      )
      Skip !
      "i" != Avar "i" + Anum 1
    ) 20 []
  )

binarySearch :: Cmd
binarySearch =
  "fvalue" != Anum (-1)!
  "mid" != Anum 0 !
  "up" != Anum 14!
  "low" != Anum 0 !
  While(Avar "low" < Avar "up")
  (
    "mid" != (Avar "low" + Avar "up") / Anum 2 !
    If (Avar "mid" == Avar "x")
    (
      "up" != Avar "low" - Anum 1!
      "fvalue" != Avar "mid"
    )
    (
      If(Avar "mid" > Avar "x")
      ("up" != Avar "mid" - Anum 1)
      ("low" != Avar "mid" + Anum 1)
    )
  ) 14 [] --XXX: Check the loop count here

facultyFunction :: Cmd
facultyFunction =
  "s" != Anum 0!
  "acc" != Anum 1!
  "i" != Anum 0!
  "n" != Anum 5!
  While(Avar "i" <= Avar "n")
  (
    "j" != Avar "i"!
    "acc" != Anum 1!
    While(Avar "j" < Avar "n")
    (
      "acc" != Avar "acc" * Avar "j"!
      "j" != Avar "j" + Anum 1
    ) 5 [] !
    "s" != Avar "acc" + Avar "s"!
    "i" != Avar "i" + Anum 1
  ) 5 []

-- First get all the variables in mkassert
agetVars :: Aexp -> Set Prelude.String -> Set Prelude.String
agetVars (Avar x) s = Set.insert x s
agetVars (Anum _) s = s
agetVars (Wnum _) s = s
agetVars (Plus l r) s = Set.union (agetVars l s) (agetVars r s)
agetVars (Minus l r) s = Set.union (agetVars l s) (agetVars r s)
agetVars (Mul l r) s = Set.union (agetVars l s) (agetVars r s)
agetVars (Div l r) s = Set.union (agetVars l s) (agetVars r s)
agetVars (Bexp0 b) s = bgetVars b s

bgetVars :: Bexp -> Set Prelude.String -> Set Prelude.String
bgetVars (Lt l r) s = Set.union (agetVars l s) (agetVars r s)
bgetVars (Gt l r) s = Set.union (agetVars l s) (agetVars r s)
bgetVars (Leq l r) s = Set.union (agetVars l s) (agetVars r s)
bgetVars (Geq l r) s = Set.union (agetVars l s) (agetVars r s)
bgetVars (Eq l r) s= Set.union (agetVars l s) (agetVars r s)
bgetVars (And l r) s = Set.union (bgetVars l s) (bgetVars r s)
bgetVars (Or l r) s = Set.union (bgetVars l s) (bgetVars r s)
bgetVars (Xor l r) s = Set.union (bgetVars l s) (bgetVars r s)
bgetVars (Not b) s = bgetVars b s
bgetVars True s = s
bgetVars False s = s

-- Now make the smt2-lib string
amkSMT :: Aexp -> Prelude.String -> Prelude.String
amkSMT (Avar x) s = s Prelude.++ " " Prelude.++ x
amkSMT (Anum n) s = s Prelude.++ " " Prelude.++ Prelude.show n
amkSMT (Wnum n) s = s Prelude.++ " " Prelude.++ Prelude.show n
amkSMT (Plus l r) s = "(+ " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
amkSMT (Minus l r) s = "(- " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
amkSMT (Mul l r) s = "(* " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
amkSMT (Div l r) s = "(/ " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
amkSMT (Bexp0 b) s = bmkSMT b s

bmkSMT :: Bexp -> Prelude.String -> Prelude.String
bmkSMT (Lt l r) s = "(< " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
bmkSMT (Gt l r) s = "(> " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
bmkSMT (Leq l r) s = "(<= " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
bmkSMT (Geq l r) s = "(>= " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
bmkSMT (Eq l r) s= "(= " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
bmkSMT (And l r) s = "(and " Prelude.++ bmkSMT l s
                      Prelude.++ " " Prelude.++ bmkSMT r s Prelude.++ ")"
bmkSMT (Or l r) s = "(or " Prelude.++ bmkSMT l s
                      Prelude.++ " " Prelude.++ bmkSMT r s Prelude.++ ")"
bmkSMT (Xor l r) s = "(xor " Prelude.++ bmkSMT l s
                      Prelude.++ " " Prelude.++ bmkSMT r s Prelude.++ ")"
bmkSMT (Not b) s = "(not " Prelude.++ bmkSMT b s Prelude.++ ") "
bmkSMT True s = "true" Prelude.++ s
bmkSMT False s = "false" Prelude.++ s

mkSMT :: Cmd -> Prelude.String 
mkSMT prog = smt where
  yu = mkassert prog (Eq (Avar "W") (Wnum 0))
       (store (store (store (\_ -> 0) "store" 1) "not" 1) "loop-count" 0)
  vars = Set.foldr' (\x y -> "(declare-const " Prelude.++ x Prelude.++ " Real) "
                             Prelude.++ y) "" (bgetVars yu Set.empty)
  smt' = "\n (assert " Prelude.++ bmkSMT yu "" Prelude.++ ")"
  smt = vars Prelude.++ smt'


main :: Prelude.IO ()
main = do
  Prelude.print (computeWcet
                 (store (store (\_ -> 0) "store" 1) "not" 1) prog3)
  Prelude.writeFile  "prog3.smt2" (mkSMT prog3)
