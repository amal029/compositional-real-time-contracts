module LanguageDrive where

import Language (Cmd(..), Aexp(..), Bexp(..), mkassert, store, computeWcet)
import qualified Prelude
import Data.Set as Set

prog1 :: Cmd
prog1 =
  Seq (Seq (If (Eq (Avar "init") (Anum ((Prelude.+ 1) 0))) (Assign "m" (Plus
    (Avar "m") (Anum ((Prelude.+ 1) 0)))) (Assign "u" (Minus (Avar "u") (Anum
    ((Prelude.+ 1) 0))))) (If (Eq (Avar "Y") (Anum ((Prelude.+ 1) 0)))
    (Assign "cond" (Bexp0 (Not (Eq (Avar "init") (Anum ((Prelude.+ 1) 0))))))
    (Assign "cond" (Bexp0 True)))) (If (Eq (Avar "cond") (Bexp0 True))
    (Assign "m" (Plus (Avar "m") (Anum ((Prelude.+ 1) 0)))) (Assign "u1"
    (Minus (Avar "u1") (Anum ((Prelude.+ 1) 0)))))

prog2 :: Cmd
prog2 =
  Seq (Seq (Assign "X" (Plus (Avar "Y") (Anum ((Prelude.+ 1) ((Prelude.+ 1)
    ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) 0)))))))))
    (Assign "X" (Mul (Avar "Y") (Anum ((Prelude.+ 1) ((Prelude.+ 1)
    ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) ((Prelude.+ 1) 0))))))))))
    (Assign "X" (Avar "Y"))


-- First get all the variables in mkassert
agetVars :: Aexp -> Set Prelude.String -> Set Prelude.String
agetVars (Avar x) s = Set.insert x s
agetVars (Anum _) s = s
agetVars (Plus l r) s = Set.union (agetVars l s) (agetVars r s)
agetVars (Minus l r) s = Set.union (agetVars l s) (agetVars r s)
agetVars (Mul l r) s = Set.union (agetVars l s) (agetVars r s)
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
amkSMT (Plus l r) s = "(+ " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
amkSMT (Minus l r) s = "(- " Prelude.++ amkSMT l s
                      Prelude.++ " " Prelude.++ amkSMT r s Prelude.++ ")"
amkSMT (Mul l r) s = "(* " Prelude.++ amkSMT l s
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
bmkSMT True s = "(= 1 1)" Prelude.++ s
bmkSMT False s = "(= 0 1)" Prelude.++ s

mkSMT :: Cmd -> Prelude.String 
mkSMT prog = smt where
  yu = mkassert prog (Eq (Avar "W") (Anum 0))
       (store (store (store (\_ -> 0) "store" 1) "not" 1) "loop-count" 0)
  vars = Set.foldr' (\x y -> "(declare-const " Prelude.++ x Prelude.++ " Int) "
                             Prelude.++ y) "" (bgetVars yu Set.empty)
  smt' = "\n (assert " Prelude.++ (bmkSMT yu "") Prelude.++ ")"
  smt = vars Prelude.++ smt'


main :: Prelude.IO ()
main = do
  Prelude.print (computeWcet
                 (store (store (store (\_ -> 0) "store" 1) "not" 1)
                  "loop-count" 0) prog2)
  Prelude.writeFile  "prog2.smt2" (mkSMT prog2)
