module Language where

import qualified Prelude

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
 | Anum Prelude.Integer
 | Wnum Prelude.Integer
 | Plus Aexp Aexp
 | Mul Aexp Aexp
 | Minus Aexp Aexp
 | Bexp0 Bexp
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

aevalT :: State Prelude.Integer -> Aexp -> Prelude.Integer
aevalT st a =
  case a of {
   Plus l r ->
    (Prelude.+) ((Prelude.+) (aevalT st l) (aevalT st r)) ((Prelude.+ 1) 0);
   Mul l r ->
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
 | While Bexp Cmd Prelude.Integer [Aexp]

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
   While b c0 n _ ->
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

replaceAWnum :: Aexp -> Prelude.Integer -> Aexp
replaceAWnum a e =
  case a of {
   Avar x' -> Avar x';
   Anum m -> Anum m;
   Wnum m -> Wnum (m Prelude.* e);
   Plus l r -> Plus (replaceAWnum l e) (replaceAWnum r e);
   Mul l r -> Mul (replaceAWnum l e) (replaceAWnum r e);
   Minus l r -> Minus (replaceAWnum l e) (replaceAWnum r e);
   Bexp0 b -> Bexp0 (replaceBWnum b e)}

replaceBWnum :: Bexp -> Prelude.Integer -> Bexp
replaceBWnum b e =
  case b of {
   Lt l r -> Lt (replaceAWnum l e) (replaceAWnum r e);
   Gt l r -> Gt (replaceAWnum l e) (replaceAWnum r e);
   Leq l r -> Leq (replaceAWnum l e) (replaceAWnum r e);
   Geq l r -> Geq (replaceAWnum l e) (replaceAWnum r e);
   Eq l r -> Eq (replaceAWnum l e) (replaceAWnum r e);
   And l r -> And (replaceBWnum l e) (replaceBWnum r e);
   Or l r -> Or (replaceBWnum l e) (replaceBWnum r e);
   Xor l r -> Xor (replaceBWnum l e) (replaceBWnum r e);
   Not b0 -> Not (replaceBWnum b0 e);
   x0 -> x0}

mkassert :: Cmd -> Bexp -> State Prelude.Integer -> Bexp
mkassert c b _UU0393_ =
  case c of {
   Skip -> b;
   Assign x0 e ->
    let {v = computeWcet _UU0393_ c} in
    let {wexp = Minus (Avar "W") (Wnum v)} in
    let {llb = replaceB b x0 e} in replaceB llb "W" wexp;
   Seq c1 c2 -> mkassert c1 (mkassert c2 b _UU0393_) _UU0393_;
   If b' t e ->
    let {v = bevalT _UU0393_ b'} in
    let {wexp = Minus (Avar "W") (Wnum v)} in
    let {lb1 = mkassert t b _UU0393_} in
    let {lb2 = mkassert e b _UU0393_} in
    Xor (And b' (replaceB lb1 "W" wexp)) (And (Not b')
    (replaceB lb2 "W" wexp));
    --FIXME: Have not changed the indices in the second copy
   While _ wc count _ ->
     let b'' = mkassert (Seq wc wc) b _UU0393_ in
     -- XXX: Now update the Wnum with (n-1) * Wnum value
     let b''' = replaceBWnum b'' (count Prelude.- 1) in
     b'''
   }
  
