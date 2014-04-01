
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Goal forall b, b || ~~b = true.
Proof. by case. Qed.

(*
Coercion is_true (b : bool) := b = true.
*)

Goal forall n m, n <= m \/ n < m.
(*
Set Printing All.
 forall n m : nat, or (is_true (leq n m)) (is_true (leq (S n) m))
*)
Abort.

Goal forall n m, (n <= m) || (n < m).
(*
Set Printing All.
forall n m : nat, is_true (orb (leq n m) (leq (S n) m))
*)
Abort.

(* Working on hypotheses *)

Section Haha.

Variables P Q : bool -> Prop.
Hypothesis P2Q : forall a b, P (a || b) -> Q a.
Goal forall a, P (a || a) -> True.
(* move=> a HPa; move: {HPa}(P2Q HPa) => HQa. by []. *)
move=> a HPa. (* rewrite /orb in HPa. *)
move: {HPa}(P2Q HPa). (* Syntax was not introduced before; it seems to do clear *) 
move => HQa. by [].
Qed.

Goal forall x, P x -> Q x -> P x.
Proof. move => x HP HQ. move {HQ}. exact HP. Qed.

Goal forall a, P (a || a) -> True.
move=> a HPa; move/P2Q: HPa => HQa. by [].
Qed.

Hypothesis Q2P : forall a b, Q (a || b) -> P a \/ P b.
Goal forall a b, Q (a || b) -> True.
move=> a b; case/Q2P => [HPa | HPb]. by []. by [].
Qed.

(* The stuff above is just a shorthand for the stuff below *)

Goal forall a b, Q (a || b) -> True.
move=> a b HQ; case: {HQ}(Q2P HQ) => [HPa | HPb]. by []. by [].
Qed.

(* Iff -- ssr will find the direction *)

Hypothesis PQequiv : forall a b, P (a || b) <-> Q a.
Goal forall a b, P (a || b) -> True.
move=> a b; move/PQequiv=> HQab. done.
Qed.

(* is the same as ... *)

Goal forall a b, P (a || b) -> True.
move=> a b; move/(iffLR (PQequiv _ _)). done.
Qed.

Check iffLR. Locate iffLR.

(* Specialization *)

Goal forall z, (forall x y, x + y = z -> z = x) -> z = 0.
move=> z; move/(_ 0 z).
Abort.

(* Working on goal *)

Goal forall a, P ((~~ a) || a).
move=> a; apply/PQequiv.
Abort.

(* is the same as ... *)

Goal forall a, P ((~~ a) || a).
move=> a; apply: (iffRL (PQequiv _ _)).
Abort.

End Haha.

(* The reflect predicate *)

Print reflect.

(* Is this more than equivalence? Not really!
   Equivalence wouldn't be well-sorted,
   but can prove both directions (see below).
Variable P : Prop.
Variable b : bool.
Lemma reflect_trivial: (P <-> b) <-> reflect P b.
Toplevel input, characters 37-48:
cnError: The term "reflect P b" has type "Set"
 while it is expected to have type "Prop".
*)

Print andP. (* : forall b1 b2 : bool, reflect (b1 /\ b2) (b1 && b2) *)
Locate andP.

Lemma andE: forall b1 b2 : bool, (b1 /\ b2) <-> (b1 && b2).
Admitted.

(* How exactly can andP and andE be applied to this goal?
   Had to look in the manual for this!

apply /andP.
Toplevel input, characters 0-11:
Error: Cannot apply view andP

apply /andE.
Toplevel input, characters 0-11:
Error: Cannot apply view andE
*)

Goal forall b1 b2, if (b1 && b2) then b1 else ~~b1||~~b2.
move => b1 b2.
case (@andE b1 b2).
case b1; case b2 => H1 H2 //=.
Qed.

Goal forall b1 b2, if (b1 && b2) then b1 else ~~b1||~~b2.
move => b1 b2.
case (@andP b1 b2). tauto.
move => H. (* what about now? *)
Abort.

Goal forall a b : bool, a -> b -> a /\ b.
move=> a b Ha Hb; apply/andP. (* and back ... apply/andP. *)
by rewrite Ha.
Qed.

Goal forall a b : bool, a /\ b -> a.
move=> a b; move/andP. (* and back ... move/andP. *)
(* move => Hab. Set Printing All. rewrite /andb in Hab. *)
case a => /= Hab //.
Show Proof. Check is_true_true.
Qed.

Print idP. (* forall b1 : bool, reflect b1 b1 *)

Goal forall b1 b2 b3, ~~ (b1 || b2)= b3.
Proof.
  move => b1 b2 b3. apply/idP/idP. Show Proof.
Abort.

Print norP. (* forall b1 b2 : bool, reflect (~~ b1 /\ ~~ b2) (~~ (b1 || b2)) *)

Goal forall b1 b2 b3, ~~ (b1 || b2)= b3.
Proof.
  move => b1 b2 b3. apply/norP/idP.
Abort.

Check iffP.
Print idP.

Goal forall P b, reflect P b.
  move => P n. apply: (iffP idP).
Abort.

Lemma reflect_half_trivial: forall P (b:bool), (P <-> b) -> reflect P b.
Proof. move => P b [H1 H2]; apply: (iffP idP); assumption. Qed.

Set Printing All. 
Lemma reflect_other_half : forall P (b:bool), reflect P b -> (P <-> b).
Proof.
  move => P b H. constructor => ?; by apply /H.
(*
  by case H => //.
  inversion H => //. congruence.
*)
Qed. Print reflect_other_half.
Check introTF.
(*
introTF
     : forall (P : Prop) (b c : bool),
       reflect P b ->
       match c return Prop with
       | true => P
       | false => not P
       end -> @eq bool b c
*)
Check elimT.
Check elimF.

Goal forall P, (P <-> false) -> (~P).
Proof.
  move => P [H1 H2] Hc. pose proof H1 Hc as H. inversion H.
  Show Proof.
Qed.
