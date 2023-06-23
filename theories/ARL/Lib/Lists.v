From stdpp Require Import prelude.

Lemma list_filter_True {A} :
  forall (l : list A), filter (const True) l = l.
Proof.
  induction l; [done |]; cbn.
  rewrite decide_True by done.
  by f_equal.
Qed.