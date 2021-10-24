module Language where

import qualified Prelude
import Debug.Trace (traceShowId)
import GHC.Prelude (RealFrac(ceiling))


type State a = Prelude.String -> a

store :: State a1 -> Prelude.String -> a1 -> State a1
store st k v k' =
  case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) k'
         k of {
   Prelude.True -> v;
   Prelude.False -> st k'}

lookup :: State a1 -> Prelude.String -> a1
lookup st =
  st

data Aexp =
   Avar Prelude.String
 | Anum Prelude.Float
 | Wnum Prelude.Integer
 | Plus Aexp Aexp
 | Mul Aexp Aexp
 | Div Aexp Aexp
 | Minus Aexp Aexp
 | Bexp0 Bexp
 deriving (Prelude.Show)

data Bexp =
   Lt Aexp Aexp
 | Gt Aexp Aexp
 | Leq Aexp Aexp
 | Geq Aexp Aexp
 | Eq Aexp Aexp
 | And Bexp Bexp
 | Or Bexp Bexp
 | Xor Bexp Bexp
 | Not Bexp
 | True
 | False
 deriving (Prelude.Show)

aevalT :: State Prelude.Integer -> Aexp -> Prelude.Integer
aevalT st a =
  case a of {
   Plus l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Mul l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Div l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Minus l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Bexp0 b -> bevalT st b;
   _ -> (Prelude.+ 1) 0}

bevalT :: State Prelude.Integer -> Bexp -> Prelude.Integer
bevalT st b =
  case b of {
   Lt l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Gt l r ->
    (Prelude.+) ((Prelude.+) (aevalT st r) (aevalT st l)) ((Prelude.+ 1) 0);
   Leq l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Geq l r ->
    (Prelude.+) ((Prelude.+) (aevalT st r) (aevalT st l)) ((Prelude.+ 1) 0);
   Eq l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   And l r ->
    (Prelude.+) ((Prelude.+) (bevalT st l) (bevalT st r)) ((Prelude.+ 1) 0);
   Or l r ->
    (Prelude.+) ((Prelude.+) (bevalT st l) (bevalT st r)) ((Prelude.+ 1) 0);
   Xor l r ->
    (Prelude.+) ((Prelude.+) (bevalT st l) (bevalT st r)) ((Prelude.+ 1) 0);
   Not b0 -> (Prelude.+) (bevalT st b0) (lookup st "not");
   _ -> (Prelude.+ 1) 0}

type Lvar = Prelude.String
  -- singleton inductive, whose constructor was Lvar
  
data Cmd =
   Skip
 | Assign Lvar Aexp
 | Seq Cmd Cmd
 | If Bexp Cmd Cmd
 | While Bexp Cmd Prelude.Integer [Aexp] Prelude.Bool

computeWcet :: State Prelude.Integer -> Cmd -> Prelude.Integer
computeWcet _UU0393_ c =
  case c of {
   Skip -> 0;
   Assign _ e -> (Prelude.+) (aevalT _UU0393_ e) (lookup _UU0393_ "store");
   Seq c1 c2 ->
    (Prelude.+) (computeWcet _UU0393_ c1) (computeWcet _UU0393_ c2);
   If b t e ->
    (Prelude.+)
      (Prelude.max (computeWcet _UU0393_ t) (computeWcet _UU0393_ e))
      (bevalT _UU0393_ b);
   While b c0 n _ _ ->
    (Prelude.+)
      ((Prelude.*)
        ((Prelude.+) (computeWcet _UU0393_ c0) (bevalT _UU0393_ b))
        n) (bevalT _UU0393_ b)}

replaceA :: Aexp -> Prelude.String -> Aexp -> Aexp
replaceA a x e =
  case a of {
   Avar x' ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           x' x of {
     Prelude.True -> e;
     Prelude.False -> Avar x'};
   Anum m -> Anum m;
   Wnum m -> Wnum m;
   Plus l r -> Plus (replaceA l x e) (replaceA r x e);
   Mul l r -> Mul (replaceA l x e) (replaceA r x e);
   Div l r -> Div (replaceA l x e) (replaceA r x e);
   Minus l r -> Minus (replaceA l x e) (replaceA r x e);
   Bexp0 b -> Bexp0 (replaceB b x e)}

replaceB :: Bexp -> Prelude.String -> Aexp -> Bexp
replaceB b x e =
  case b of {
   Lt l r -> Lt (replaceA l x e) (replaceA r x e);
   Gt l r -> Gt (replaceA l x e) (replaceA r x e);
   Leq l r -> Leq (replaceA l x e) (replaceA r x e);
   Geq l r -> Geq (replaceA l x e) (replaceA r x e);
   Eq l r -> Eq (replaceA l x e) (replaceA r x e);
   And l r -> And (replaceB l x e) (replaceB r x e);
   Or l r -> Or (replaceB l x e) (replaceB r x e);
   Xor l r -> Xor (replaceB l x e) (replaceB r x e);
   Not b0 -> Not (replaceB b0 x e);
   x0 -> x0}

mkassert :: Cmd -> Bexp -> State Prelude.Integer -> Prelude.Integer ->
            (Bexp, Prelude.Integer)
mkassert Skip b _ mult = (b, mult) 

mkassert (Assign x0 e) b state mult = (llb, mult)
  where
    v = computeWcet state (Assign x0 e)
    b' = replaceB b x0 e
    llb = replaceB b' "W" (Minus (Avar "W") (Wnum (v Prelude.* mult)));

mkassert (Seq c1 c2) b state mult = (b'', mult)
  where
    (b', _) = mkassert c2 b state mult
    (b'', _) = mkassert c1 b' state mult

mkassert (If b' t e) b state mult = (b'', mult)
  where
    v = bevalT state b'
    wexp = Minus (Avar "W") (Wnum (v Prelude.* mult))
    (lb1, _) = mkassert t b state mult
    (lb2, _) = mkassert e b state mult
    b'' = Xor (And b' (replaceB lb1 "W" wexp))
          (And (Not b') (replaceB lb2 "W" wexp))

--FIXME: Indices
mkassert (While b' wc count _ unroll) b state mult = (b'', mult)
  where
    v = bevalT state b'
    (b'', _) =
      --FIXME: Fix this to make it more general later
      if unroll Prelude.&& Prelude.even count then
        let cm = (count `Prelude.div` 2) in
        let (y, m) = mkassert (Seq wc wc) b state (cm Prelude.* mult) in
          (replaceB y "W" (Minus (Avar "W")
                           (Wnum (v Prelude.* (cm Prelude.+ 1) Prelude.* mult)))
          , m)
      else
        let tt = (count Prelude.+ 1) Prelude.* mult in
        let (y, m) = mkassert wc b state (count Prelude.* mult) in
          (replaceB y "W" (Minus (Avar "W") (Wnum (v Prelude.* tt))), m)
