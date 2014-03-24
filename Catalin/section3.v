(******************************************************************************)
(* Solutions of exercises : A script language for structured proofs           *)
(******************************************************************************)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(******************************************************************************)
(* Exercise 3.2.1                                                             *)
(******************************************************************************)

Section Tauto.

Variables A B C : Prop.

(* The exact tactic takes its argument on top of the goal stack *)
Lemma tauto1 : A -> A.
Proof. done. Qed.

(* exact: hAB behaves like (by apply: hAB) and hence finds the hypothesis A
in the context needed to solve the goal *)
Lemma tauto2 : (A -> B) -> (B -> C) -> A -> C.
Proof. move=> ab bc a. apply: bc. apply: ab. exact a. Qed.

Lemma tauto3 : A /\ B <-> B /\ A.
Proof. by split=>H; elim: H=> H1 H2. Qed.
  
End Tauto.

(******************************************************************************)
(* Exercise 3.2.2                                                             *)
(******************************************************************************)

Section MoreBasics.

Variables A B C : Prop.
Variable P : nat -> Prop.

Lemma foo1 : ~(exists x, P x) -> forall x, ~P x.
Proof.
  move=>Hnex x HP. apply: Hnex. by exists x.
Qed.

Lemma foo2 : (exists x, A -> P x) -> (forall x, ~P x) -> ~A.
Proof.
  case=>x Hx HPx HA. apply: (HPx x). by apply Hx.
Qed.

End MoreBasics.

(******************************************************************************)
(* Exercise 3.2.3                                                             *)
(******************************************************************************)

(* Try Search "<=" to see the various notations featuring <= *)

(* The first line of the returned answer gives the name of
   the predicate (leq) *)
Search "_ <= _".

(* The Print command shows that leq is defined using subtraction *)
Print leq.

(* This time we see that the first line of the answer gives the *)
(*answer: there is no constant defining "<" but the notation hides a *)
(* defintiion using leq *)

Search "_ < _".

Lemma tuto_subnn : forall n : nat, n - n = 0.
Proof.
  by elim=>[|n' IH].
Qed.
  
Lemma tuto_subn_gt0 : forall m n, (0 < n - m) = (m < n).
Proof.
  elim => [| m' IHm] [| n'] //. exact: IHm.
Qed.

(* XXX started feeling a bit lost *)
Lemma tuto_subnKC : forall m n : nat, m <= n -> m + (n - m) = n.
Proof.
  elim => [| m' IHm] [| n'] H //. (* unfold subn, addn => /=. *)
  Search _ (_.+1 + _ = _.+1).
  rewrite addSn. by rewrite IHm.
Qed.

(* XXX started feeling completely lost;
   - natural subtraction is anything but intuitive
   - even if I were given all the needed lemmas,
     I would still not know how to apply them *)
Lemma tuto_subn_subA : forall m n p, p <= n -> m - (n - p) = m + p - n.
Proof.
  move => m n p h.
  (* peaked to get to these *)
  Check subnK. Check subn_add2r.
  (* they didn't explain rewrite, and selectors yet! *)
  have magic := subnK h.
  rewrite -{2}magic. by rewrite subn_add2r.  
Qed.

(******************************************************************************)
(* Exercise 3.5.1                                                             *)
(******************************************************************************)

(* The Check instruction only gives the type of a constant, the *)
(*statement of a lemma. The Print command gives the body of the *)
(*definition, and possibly some extra information (scope, implicit *)
(*arguments,...). Print should not be used in general on lemmas *)
(* since the body of a proof is seldom relevant...*)

Print edivn.
Print edivn_rec.
Print edivn_spec.
(* The edivn_spec is defined as a CoInductive predicate. The intended *)
(* meaning is not to define an coinductive structure, but rather an *)
(* inductive one. CoInductive in this case indeed behaves as Inductive *)
(*but does not generate an induction principle, which would be is *)
(*useless in this case. *)

(* XXX Their crappy lemma -- proof doesn't even work till the end *)
Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
  move => m. rewrite /edivn. move => [| d] /=; first done.
  rewrite -{1}[m]/(0*d.+1 + m). Check (leqnn m).
  (* this is really magic *)
  elim: m {-2}m 0 (leqnn m) => [| n IHn] [|m] q //=; [];
    rewrite ltnS => le_mn. Check subn_if_gt.
  rewrite subn_if_gt. case: (ltnP m d) => [// | le_dm].
  specialize (IHn (m - d) (q.+1)).
  rewrite mulSnr in IHn.
  rewrite -addnA in IHn.
  rewrite (addSn d) in IHn.
  rewrite subnKC in IHn; last done. apply IHn.
  apply: leq_trans le_mn; exact: leq_subr.
(* their proof works shit:
  Check subnK le_dm. Check addSn.
  rewrite -{1}(subnK le_dm). rewrite -addSn. rewrite addnA. 
  Check mulSnr.
  apply IHn.
*)

(******************************************************************************)
(* Exercise 3.5.2                                                             *)
(******************************************************************************)

(* At this point, the top of the goal stack was featuring three *)
(*natural numers: an induction on the first one generated two subgoals. *)
(*In the second subgoal, corresponding to the inductive case, the *)
(*generated natural number and induction hypothesis have  been *)
(*introduced by the branching intro pattern [| n IHn], which leaves *)
(*the first subgoal, corresponding to the base case of the induction, *)
(*unchanged. Then [|m] performs in both subgoals a case analysis on the *)
(*second natural number. This case analysis again leads to two new *)
(*subgoal for each initial branch (which makes four subgoals). In the *)
(*second case of the analysis, the new natural number is introduced *)
(*and named m. Then the third natural number is uniformly introdued in *)
(*the four cases under the name q. Finally the //= switch simplifies *)
(*in the four bracnhes and closes the goals that have become trivial *)
(*(i.e. which are solved by done). *)

(******************************************************************************)
(* Exercise 3.5.3                                                             *)
(******************************************************************************)

(* The pattern [// | le_dm] closes the first subgoal and introduces an *)
(*hypothesis named le_dm in the second subgoal. This is equivalent to *)
(* // le_dm. *)

(******************************************************************************)
(* Exercise 3.5.4                                                             *)
(******************************************************************************)

(* Replacing (ltnP m d) by ltnP does not change the behaviour of the *)
(*script: Coq's unification is powerful enough to guess the arguments *)
(*in this case since there is only one instance of the comparison in *)
(* (_ <_) the goal. Arguments are mandatory only in the case the frist *)
(*occurrence of the comparison is not the one the user whould like to *)
(*pick as support for ase analysis. *)

Check ltnP.
Print ltn_xor_geq.

(* For any two natural numbers n and m, (ltn_xor_geq m n) is a binary *)
(*relation on boolean. Its inductive definition has two constructors *)
(*and states that *)
(* - (false, true) is in the relation(ltn_xor_geq m n) as soon as 
     m < n *)
(* - (true, false) is in the relation(ltn_xor_geq m n) as soon as 
     n <= m *)
(* The inductive construction implies that these two rules are the *)
(*only ways to populate the relation.*)
(* Now the theorem:*)
(* ltnP :  forall m n : nat, ltn_xor_geq m n (n <= m)(m < n)*)
(*proves that for any two natural numbers m and n, there are only two*)
(*possible situations:*)
(* - either m < n (first rule of the relation definition), and in this *)
(*case n <= m = false and m < n = true *)
(* - or n <= m (second rule of the relation definition, and in this *)
(*case n <= m = true and m < n = false *)
(* A case analysis on this result hence generates two subgoals, one *)
(*for each constructor of ltn_xor_gep. In each subgoal the hypothesis *)
(*of the rule (repectively m < n and n <= m) appears on the stack. Also *)
(*every occurrence of (n <= m) and (m < n) is replaced by the value *)
(*imposed by the ltn_xor_gep constructor used in the branch.*)

CoInductive tuto_compare_nat (m n : nat) : bool -> bool -> bool -> Set :=.

(* Let's check against what is defined in the ssrnat library *)
Print compare_nat.

Lemma tuto_ltngtP : forall m n, compare_nat m n (m < n) (n < m) (m == n).
Admitted.




