Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lqa.

Definition state {A : Set} := string -> A.

Check @state string.

(* Making a new state *)
Definition K {A: Set} (n : A) : state := fun _ => n.

Definition Store {A : Set} (st : @state A) (k : string) (v : A): state :=
  fun k' => if eqb k' k then v else (st k').

Definition lookup {A:  Set} (st : @state A) (s : string) : A := st s.

Definition mymy := Store (K 0) "tutu" 10.

Lemma st_update_xyne {A : Set} : forall (st : @state A), forall(x y : string),
  forall(v : A), (y <> x) -> (Store st x v) y = (st y).
Proof.
  intros. unfold Store. rewrite <- eqb_neq in H.
  rewrite H. reflexivity.
Qed.

(* Just made it a nat type for now *)
Inductive aexp : Set :=
| Avar : forall (x : string), aexp
| Anum : forall (m : nat), aexp
| Plus : forall (l r : aexp), aexp
| Mul  : forall (l r : aexp), aexp
| Minus: forall (l r: aexp), aexp.

(* The evaluation function for aexp *)
Fixpoint aeval (st : @state nat) (a : aexp) :=
  match a with
  | Avar x => (st x)
  | Anum m => m
  | Plus l r => (aeval st l) + (aeval st r)
  | Mul  l r => (aeval st l) * (aeval st r)
  | Minus l r => (aeval st l) - (aeval st r)
  end.

Inductive bexp : Set :=
| Lt : forall (l r : aexp), bexp
| Gt : forall (l r : aexp), bexp
| Leq : forall (l r : aexp), bexp
| Geq : forall (l r : aexp), bexp
| Eq : forall (l r : aexp), bexp
| And : forall (l r : bexp), bexp
| Or : forall (l r : bexp), bexp
| True : bexp
| False : bexp.

(* The bexp evaluation *)

Fixpoint beval (st : @state nat) (b : bexp) : bool :=
  match b with
  | True => true
  | False => false
  | Lt l r => Nat.ltb (aeval st l) (aeval st r)
  | Leq l r => Nat.leb (aeval st l) (aeval st r)
  | Eq l r => Nat.eqb (aeval st l) (aeval st r)
  | Geq l r => Nat.leb (aeval st r) (aeval st l)
  | Gt l r => Nat.ltb (aeval st r) (aeval st l)
  | And l r => (beval st l) && (beval st r)
  | Or l r => (beval st l) || (beval st r)
  end.

(* Execution time semantics of aexp *)
Fixpoint aevalT (st : @state nat) (a : aexp) : nat :=
  match a with
  | Avar x => 1
  | Anum m => 1
  | Plus l r => (aevalT st l) + (aevalT st r) + (lookup st "+")
  | Mul  l r => (aevalT st l) * (aevalT st r) + (lookup st "*")
  | Minus l r => (aevalT st l) - (aevalT st r) + (lookup st "-")
  end.

(* Execution time semantics of bexp *)

Fixpoint bevalT (st : @state nat) (b : bexp) : nat :=
  match b with
  | True => 1
  | False => 1
  | Lt l r => (aevalT st l) + (aevalT st r) + (lookup st "<")
  | Leq l r => (aevalT st l) + (aevalT st r) + (lookup st "<=")
  | Eq l r => (aevalT st l) + (aevalT st r) + (lookup st "=")
  | Geq l r => (aevalT st r) + (aevalT st l) + (lookup st ">=")
  | Gt l r => (aevalT st r) + (aevalT st l) + (lookup st ">")
  | And l r => (bevalT st l) + (bevalT st r) + (lookup st "and")
  | Or l r => (bevalT st l) + (bevalT st r) + (lookup st "or")
  end.

(* The lvar type *)
Inductive lvar : Set :=
| Lvar : forall (x : string), lvar.

(* Now the commands *)

Inductive cmd : Set :=
| Skip : cmd
| Assign : forall (x : lvar), forall(e : aexp), cmd
| Seq : forall (c1 c2 : cmd), cmd
| If : forall(b : bexp), forall(t e : cmd), cmd
| While : forall (b : bexp), forall (c : cmd), cmd.

(* The semantics of these cmd statements *)

Inductive exec : @state nat -> @state nat -> nat -> cmd -> @ state nat -> nat -> Prop :=
| Eskip : forall (G st : state), forall (W : nat), exec G st W Skip st (W + 0)

| Eassign : forall (G st st' : @state nat), forall (W : nat), forall (x : string),
  forall (e : aexp),
    exec G st W (Assign (Lvar x) e) (Store st x (aeval st e)) (W + (aevalT G e))

| Eseq : forall (G st st' st'' : @state nat), forall (W X1 X2 : nat), forall (c1 c2 : cmd),
    exec G st W c1 st' (W + X1) -> exec G st' (W + X1) c2 st'' (W + X1 + X2)
    -> exec G st W (Seq c1 c2) st'' (W + X1 + X2)

| EifT : forall (G st st' st'' : @state nat), forall (W X1 X2 : nat), forall (e t : cmd),
  forall (b : bexp), (beval st b = true) -> exec G st W t st' (W + X1) ->
                     exec G st W e st'' (W + X2) -> exec G st W (If b t e) st'
                                                         (W + X1)

| EifF : forall (G st st' st'' : @state nat), forall (W X1 X2 : nat), forall (e t : cmd),
  forall (b : bexp), (beval st b = false) -> exec G st W t st' (W + X1) ->
                     exec G st W e st'' (W + X2) -> exec G st W (If b t e) st''
                                                         (W + X2)

| EwhileF : forall(G st : @state nat), forall (W : nat), forall (c : cmd),
  forall (b : bexp), (beval st b = false)
                -> exec G st W (While b c) st (W + 0 + (bevalT G b))

| EwhileT: forall(G st st' st'' : @state nat), forall (W X1 X2 : nat), forall (c : cmd),
  forall (b : bexp), (beval st b = true) -> exec G st W c st' (W + X1)
                -> exec G st' (W + X1) (While b c) st'' (W + X1 + (bevalT G b))
                -> exec G st W (While b c) st''
                       (W + (X1 + (bevalT G b)) * (lookup G "loop-count") +
                          (bevalT G b)).

(* Now prove determinism of the semantics and see if it any easier than Agda *)

Lemma Δ_exec : forall (c : cmd), forall (Γ st st' st'' : @state nat), forall (W W' W'' : nat),
    (exec Γ st W c st' W') -> (exec Γ st W c st'' W'') ->
    st' = st'' /\ W' = W''.
Proof.
  intros c Γ st st' st'' W W' W'' E1 E2.
  generalize dependent st''.
  generalize dependent W''.
  induction E1. intros. inversion E2. subst.
  auto. intros. inversion E2. subst. auto.
  intros. inversion E2. subst.
  set (yt := IHE1_1 (W + X0) st'0 H4).
  destruct yt. rewrite <- H in H7. rewrite <- H0 in H7.
  set (yt := IHE1_2 (W + X1 + X3) st''0 H7).
  destruct yt. rewrite H1.
  split. reflexivity.
  set (tt := PeanoNat.Nat.add_cancel_l X2 X3 (W + X1)).
  destruct tt. auto.
  intros. inversion E2. subst. 
  set (yt := IHE1_1 (W + X0) st''0 H9); destruct yt.
  rewrite H0, H1. auto.
  subst. rewrite H6 in H. contradict H.
  apply Bool.diff_false_true.
  intros; inversion E2; subst.
  rewrite H6 in H. contradict H. apply Bool.diff_true_false. 
  set (yt := IHE1_2 (W + X3) st''0 H10); destruct yt.
  rewrite H0, H1. auto.
  intros; inversion E2; subst; auto.
  rewrite H2 in H. contradict H.
  apply Bool.diff_true_false.
  intros; inversion E2; subst.
  rewrite H7 in H. contradict H.
  apply Bool.diff_false_true. 
  set (yt := IHE1_1 (W + X0) st'0 H6); destruct yt.
  rewrite <-H0, <-H1 in H9.
  set (yt := IHE1_2 (W + X1 + (bevalT G b)) st''0 H9); destruct yt.
  rewrite H3. subst. split. reflexivity. lia.
Qed.

(* Now do the new wcet semantics *)

Lemma states_eq :
  forall (c : cmd), forall (Γ st st' st'' : @state nat), forall (W1 W2 W' W'': nat),
    (exec Γ st W1 c st' W') -> (exec Γ st W2 c st'' W'') ->
     st' = st''. 
Proof.
  intros c Γ st st' st'' W1 W2 W' W'' E1 E2.
  generalize dependent st''. generalize dependent W''.
  generalize dependent W2.
  induction E1.

  (* The skip statement *)
  intros; inversion E2; subst; reflexivity.
  (* Now the assign statement *)
  intros; inversion E2; subst. reflexivity.
  (* The seq case *)
  intros; inversion E2; subst.
  set (yt := IHE1_1 W2 (W2 + X0 ) st'0 H4).
  rewrite <- yt in H7. set(yt1 := IHE1_2 (W2 + X0) (W2 + X0 + X3) st''0 H7).
  rewrite <- yt1. reflexivity.
  (* The If statement *)
  intros; inversion E2; subst.
  set (yt := IHE1_1 W2 (W2 + X0) st''0 H9).
  rewrite <- yt; reflexivity.    (* true true *)
  (* true false *)
  rewrite H6 in H; contradict H; apply Bool.diff_false_true.
  intros; inversion E2; subst.
  (* false true *)
  rewrite H6 in H. contradict H. apply Bool.diff_true_false. 
  (* false false *)
  set (yt := IHE1_2 W2 (W2 + X3) st''0 H10); rewrite <- yt; reflexivity.
  (* While *)
  intros; inversion E2; subst.
  reflexivity.                  (* false *)
  (* false true *)
  rewrite H2 in H. contradict H. apply Bool.diff_true_false. 
  (* true false *)
  intros; inversion E2; subst.
  rewrite H7 in H. contradict H. apply Bool.diff_false_true. 
  (* true true *)
  set (yt := IHE1_1 W2 (W2 + X0) st'0 H6).
  rewrite <- yt in H9.
  set (yt1 := IHE1_2 (W2 + X0) (W2 + X0 + (bevalT G b)) st''0 H9).
  rewrite <- yt1; reflexivity.
Qed.

Lemma cancel_exec_time : forall (c : cmd),
  forall (Γ st st' st'' : @state nat), forall (W1 W2 W' W'': nat),
    (exec Γ st W1 c st' (W1 + W')) -> (exec Γ st W2 c st'' (W2 + W'')) ->
      (W' = W'').
Proof.
  induction c.
  (* Skip *)
  intros. inversion H; inversion H0. subst; lia.
  (* assign *)
  intros; inversion H; inversion H0; subst. lia.
  (* Seq *)
  intros. inversion H; inversion H0; subst.
  set (yt := states_eq c1 Γ st st'0 st'1 W1 W2 (W1 + X1) (W2 + X0) H8 H17).
  rewrite <- yt in H18.
  set (ytt := IHc1 Γ st st'0 st'1 W1 W2 X1 X0 H8 H17).
  rewrite ytt in H6. rewrite ytt in H9.
  set (ytt2 := IHc2 Γ st'0 st' st'' (W1 + X0) (W2 + X0) X2 X3 H9 H18).
  rewrite ytt2 in H6. lia.
  (* If-else *)
  intros; inversion H. subst.
  Focus 1. inversion H0. subst.
  (* true-true *)
  set (yt := IHc1 Γ st st' st'' W1 W2 X1 X0 H10 H14).
  rewrite yt in H7. lia.
  (* true-false *)
  subst.  rewrite H13 in H9. contradict H9.
  apply Bool.diff_false_true. 
  subst. inversion H0. subst.
  (* false-true *)
  rewrite H13 in H9. contradict H9. apply Bool.diff_true_false. 
  (* false-false *)
  subst. set (yt := IHc2 Γ st st' st'' W1 W2 X2 X3 H11 H15).
  rewrite yt in H7. lia.
  (* While *)
  intros; inversion H; subst.
  Focus 1. inversion H0.
  (* False *)
  lia. subst.
  (* false- true *)
  rewrite H9 in H7. contradict H7. apply Bool.diff_true_false. 
  inversion H0. subst.
  rewrite H11 in H7. contradict H7. apply Bool.diff_false_true.
  (* true-true *)
  subst.
  set (yt := IHc Γ st st'0 st'1 W1 W2 X1 X0 H9 H13).
  rewrite yt in H3. rewrite yt in H10. lia.
Qed.  

(* Theorem for WCET of skip *)

Lemma skip_sound : forall(Γ st st' : @state nat), forall (W W' X : nat),
    exec Γ st W Skip st' W' -> (W = X) -> (W' = X).
Proof.
  intros. inversion H. subst. auto.
Qed.  

Lemma assign_sound: forall(Γ st st' : @state nat), forall (W W' X : nat),
  forall (x : string), forall (e : aexp),
    exec Γ st W (Assign (Lvar x) e) st' W' -> W' = (W + (aevalT Γ e)).
Proof.
  intros. inversion H. subst. reflexivity.
Qed.

Lemma seq_sound : forall(Γ st st' st'' st''' : @state nat), forall (W W' X1 X2 : nat),
  forall (c1 c2 : cmd), exec Γ st W (Seq c1 c2) st' W' ->
                   exec Γ st W c1 st'' (W + X1) -> exec Γ st'' W c2 st''' (W + X2)
                   -> W' = (W + X1 + X2).
Proof.
  intros. inversion H. subst.
  set (yt := Δ_exec c1 Γ st st'' st'0 W (W + X1) (W + X0) H0 H7).
  destruct yt. rewrite <- H2 in H10.
  set (ytt := cancel_exec_time c2 Γ st'' st''' st' W (W + X0) X2 X3 H1 H10).
  rewrite ytt. lia.
Qed.


Lemma ife_sound : forall(Γ st st' st'' st''' : @state nat), forall (W W' X1 X2 : nat),
  forall (b : bexp), forall (t e : cmd),
    exec Γ st W t st' (W + X1) -> exec Γ st W e st'' (W + X2)
    -> exec Γ st W (If b t e) st''' W' -> (W' <= W + Nat.max X1 X2).
Proof.
  intros. inversion H1. subst.
  set (yt := Δ_exec t Γ st st' st''' W (W + X1) (W + X0) H H11).
  destruct yt. lia.
  subst. set (yt := Δ_exec e Γ st st'' st''' W (W + X2) (W + X3) H0 H12).
  destruct yt. lia.
Qed.

Lemma while_sound : forall(Γ st st' st'' st''' : @state nat), forall (W W' X1 X2 : nat),
  forall (b : bexp), forall (c : cmd), exec Γ st W c st' (W + X1)
                             -> exec Γ st W (While b c) st' W'
                             -> W' <=
                                 (W + (X1 + (bevalT Γ b)) *
                                        (lookup Γ "loop-count") + (bevalT Γ b)).
Proof.
  intros. inversion H0. subst. lia.
  subst. set (yt := Δ_exec c Γ st st' st'0 W (W + X1) (W + X0) H H7).
  destruct yt. lia.
Qed.

(* Now we want to write a function that computes the worst case time *)

Fixpoint compute_wcet (Γ : @state nat) (c : cmd): nat :=
  match c with
  | Skip => 0
  | Assign lx e => aevalT Γ e
  | Seq c1 c2 => (compute_wcet Γ c1) + (compute_wcet Γ c2)
  | If b t e => Nat.max (compute_wcet Γ t) (compute_wcet Γ e) + (bevalT Γ b)
  | While b c => ((compute_wcet Γ c) + (bevalT Γ b)) * (lookup Γ "loop-count")
                + (bevalT Γ b)
  end.

(* Now prove that the computed wcet is really the max *)
Theorem wcet_sound : forall (Γ st st' : @state nat), forall (c : cmd), forall (W W' : nat),
  exec Γ st W c st' W' -> W' <= W + (compute_wcet Γ c).
Proof.
  intros. induction H. simpl. reflexivity.
  simpl. reflexivity. simpl; lia. simpl; lia. simpl; lia. simpl; lia. simpl.
  set (yt := lookup G "loop-count"). set (ty := (bevalT G b)).
  rewrite Nat.mul_add_distr_r. rewrite Nat.mul_add_distr_r.
  set (rt := ty * yt). set (er := X1 * yt).
  set (ui := compute_wcet G c * yt). rewrite Nat.add_assoc.
  rewrite Plus.plus_assoc_reverse.  set (df := Nat.add_assoc ui rt ty).
  rewrite <- df. set (err := rt + ty). rewrite  Nat.add_assoc.
  set (ll := Nat.add_comm er err). set (lli := Nat.add_comm ui err).
  rewrite  <- Nat.add_assoc. rewrite  <- Nat.add_assoc.
  rewrite ll, lli. rewrite Nat.add_assoc, Nat.add_assoc.
  set (uii := W + err).
  set (yuu := Plus.plus_le_reg_l X1 (compute_wcet G c) W IHexec1).
  set (tyty := Mult.mult_le_compat_r X1 (compute_wcet G c) yt yuu).
  lia.
Qed.
