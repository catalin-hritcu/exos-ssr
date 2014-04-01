Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset.

Goal forall n m, n <= m -> m - n + n = m.
Proof.
  move => n m lenm. elim : n m lenm => [m | n IHn m lt_n_m].
Abort.

Goal forall n, S n = 3.
move => n. elim: (S n). Focus 2.
Abort.

Goal True.
have: 42 = 42 by [].
Abort.

Goal True.
have: forall xs, xs = nil \/ exists h, exists t, xs = h :: t.
Abort.

Goal forall x : nat, False.
suff : forall x y : nat, x = y by
  move => H n; have: 0 = 1 by exact (H 0 1); by move => Hc //.
Abort.

Goal forall n m, n + m = m + n.
move => n m. wlog: / (n <= m). (* suff n <= m -> n + m = m + n *)
Abort.

Axiom le_gt_dec : forall n m, {n <= m} + {n > m}.

Lemma quo_rem_unicity : forall d q1 q2 r1 r2 : nat,
  q1 * d + r1 = q2 * d + r2 ->
  r1 < d ->
  r2 < d ->
  (q1,r1) = (q2,r2).
Proof.
move => d q1 q2 r1 r2.
wlog: q1 q2 r1 r2 / q1 <= q2.
  move => H. case (le_gt_dec q1 q2); last symmetry; auto.
Admitted.
