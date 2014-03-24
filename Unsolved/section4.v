(******************************************************************************)
(* Solutions of exercises : Small scale reflection, first examples            *)
(******************************************************************************)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(******************************************************************************)
(* Exercise 4.1.1                                                             *)
(******************************************************************************)

(* The proof goes by case analysis on the truth table, applying the *)
(*appropriate constructor of the reflect predicate in every meaningful *)
(*case. The other case ask a proof of False in a conctext where False *)
(*can be obtained as a hypothesis after destructing a conjunction (the *)
(*last case tactic) *)

Lemma tuto_andP : forall b1 b2 : bool, reflect (b1 /\ b2) (b1 && b2).
Admitted.

(* Again this lemma is a macro for a cacse analysis on the truth table *)
(*of b1 b2 and (b1 || b2) *)

Lemma tuto_orP : forall b1 b2 : bool, reflect (b1 \/ b2) (b1 || b2).
Admitted.

(******************************************************************************)
(* Exercise 4.1.2                                                             *)
(******************************************************************************)

(* The first solution follows the hint given in the tutorial. In fact *)
(* it is sufficient to perform case analysis on the constructor of the *)
(*reflect hypothesis as done in the second solution. *)
Lemma tuto_iffP : forall (P Q : Prop) (b : bool),
      reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Admitted.


Lemma alternate_tuto_iffP : forall (P Q : Prop) (b : bool),
      reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Admitted.

(******************************************************************************)
(* Exercise 4.2.1                                                             *)
(******************************************************************************)

(*We use a section to factorize the type of elements in the *)
(*sequences*)

Section Exo_4_2_1.

Variable A : Type.

(* We use implicit type annotations to avoid casting quantified *)
(*variables : *)
Implicit Types s : seq A.
Implicit Types x : A.

(* The type of x has been declared implicit, hence the type of s1 and *)
(*s2 and inferred: *)
Fixpoint tuto_cat s1 s2 :=
match s1 with
  |[::] => s2
  | x :: s' => x :: (tuto_cat s' s2)
end.

(* Using the ssreflect pattern conditional this code can be shrinked *)
(*into the actual program present in the seq library:*)
Fixpoint alternate_tuto s1 s2 :=
  if s1 is x :: s' then x :: (tuto_cat s' s2) else s2.


(* The proof goes by induction on the first list. We do not need to be *)
(*general with respect to the second list, hence we introduce it *)
(*before the induction. The first case is solved on the fly by the //= *)
(*simple+solve switch, and x and s1 are introduced in the remaining *)
(*goal. The last hypothesis is directly rewritten without being *)
(*introduced, generating an equality between convertible terms. This *)
(*equality being trivial it is solved by the prenex 'by' tactic *)
Lemma tuto_size_cat : forall s1 s2,
   size (s1 ++ s2) = size s1 + size s2.
Admitted.

(* We use again a pattern conditional *)
Fixpoint tuto_last (x : A)(s : seq A) {struct s} := 
  if s is x' :: s' then tuto_last x' s' else x.

(* Again an induction on the first list *)
Lemma tuto_last_cat : forall x s1 s2,
  last x (s1 ++ s2) = last (last x s1) s2.
Admitted.

Fixpoint tuto_take n s {struct s} :=
  match s, n with
  | x :: s', n'.+1 => x :: take n' s'
  | _, _ => [::]
  end.


(* Here we have two options: a recursion on the nat or on the seq.*)
(* Decreazing on the seq has better compositional properties: it *)
(*allows more fixpoints further defined to decrease structurally *)
Fixpoint tuto_drop n s {struct s} :=
  match s, n with
  | _ :: s', n'.+1 => drop n' s'
  | _, _ => s
  end.

Definition tuto_rot n s := drop n s ++ take n s.

Lemma tuto_cat_take_drop : forall (n0 : nat)(s : seq A),
  take n0 s ++ drop n0 s = s.
Admitted.

Lemma tuto_rot_addn : forall m n s, m + n <= size s ->
  rot (m + n) s = rot m (rot n s).
Admitted.

(* Look at the source of the seq.v file for a shorter proof! *)

End Exo_4_2_1.
(******************************************************************************)
(* Exercise 4.2.2                                                             *)
(******************************************************************************)

Section Exo_4_2_2.

Variable A : Type.

(* We use implicit type annotations to avoid casting quantified *)
(*variables : *)
Implicit Types s : seq A.
Implicit Types x : A.

(* We fix an arbitrary predicate a *)
Variable a : pred A.

(* We use again a pattern conditional *)
Fixpoint tuto_count s := if s is x :: s' then a x + tuto_count s' else 0.

Lemma tuto_count_predUI : forall a1 a2 s,
 count (predU a1 a2) s + count (predI a1 a2) s = count a1 s + count a2 s.
Admitted.

(* After closing the section, tuto_count_filter has the type required *)
(* by the exercise *)
Lemma tuto_count_filter : forall s, count a s = size (filter a s).
Admitted.

End Exo_4_2_2.

(******************************************************************************)
(* Exercise 4.3.1                                                             *)
(******************************************************************************)

Section Exo_4_3_1.

(* We fix an arbitrary eqType T *)
Variable T : eqType.

(* We use implicit type annotations to avoid casting quantified *)
(*variables *)
Implicit Types x y : T.
Implicit Type b : bool.

Lemma tuto_eqxx : forall x, x == x.
Admitted.

(* First solution *)
Lemma tuto_predU1l : forall x y b, x = y -> (x == y) || b.
Admitted.

(* Second solution. The syntax move/eqP-> is equivalent to *)
(*move/eqP => ->, i.e. it applies the view to the top element of the *)
(*goal stack and rewrites the term obtains immediatly without *)
(*introducing it in the context. Similarily, move-> is equaivalent to *)
(*move=> -> and rewrite the top element of the goal (which should be *)
(*an equality) in the rest of the goal, without introducing it in the context *)

Lemma tuto_predU1l_alt_proof : forall x y b, x = y -> (x == y) || b.
Admitted.

(* The proof script is the same in both branches thanks to the *)
(* symmetry of the view mechanism. Remeber the 'by' tactical contains *)
(* the 'split' tactic and hence solves the goal after the last *)
(* assumption interpretation move/eqP. *)
Lemma tuto_predD1P : forall x y b, reflect (x <> y /\ b) ((x != y) && b).
Admitted.

(* Remember that _ != _ denotes the boolean disequality *)
(* Coq's unification is able to infer from the goal the arguments to *)
(* provide to the eqP lemma*)
Lemma tuto_eqVneq : forall x y, {x = y} + {x != y}.
Admitted.

End Exo_4_3_1.