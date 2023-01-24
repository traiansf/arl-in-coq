From stdpp Require Import prelude.
From Coq Require Import ClassicalEpsilon.
From sets Require Import Ensemble.
From ARL Require Import Traces TransitionSystem CTL.

Section sec_fix_points.

Context
  `{TransitionSystem}
  (ψ : Ensemble idomain)
  .

Definition EF_ts_fixed_point_functor (X : Ensemble idomain) : Ensemble idomain :=
  fun a => a ∈ ψ \/ exists b, transition a b /\ b ∈ X.

Lemma EF_ts_pre_fixpoint :
  pre_fixpoint EF_ts_fixed_point_functor (EF_ts ψ).
Proof.
  intro a.
  intros [Ha | (b & Hab & tr & Htr & Hlst)];
    [by exists []; split; [repeat constructor |] |].
  exists (b :: tr).
  split; [| by rewrite last_cons].
  by apply ForAllConsecutivePairsList_cons.
Qed.

Lemma EF_ts_post_fixpoint :
  post_fixpoint EF_ts_fixed_point_functor (EF_ts ψ).
Proof.
  intros a (tr & Htr & Hlst).
  destruct tr; [by left |].
  right; exists i.
  apply ForAllConsecutivePairsList_cons in Htr as [Hai Htr].
  rewrite last_cons in Hlst.
  by split; [| exists tr].
Qed.

Lemma EF_ts_fixpoint :
  fixpoint EF_ts_fixed_point_functor (EF_ts ψ).
Proof.
  split.
  - apply (EF_ts_pre_fixpoint x).
  - apply (EF_ts_post_fixpoint x).
Qed.

Lemma EF_ts_least_pre_fixpoint A :
  pre_fixpoint EF_ts_fixed_point_functor A ->
  EF_ts ψ ⊆ A.
Proof.
  intros Hpre.
  intros a (tr & Htr & Hlst).
  remember (a :: tr) as atr.
  revert a tr Htr Heqatr Hlst.
  induction atr; [by inversion 2 |].
  inversion 2; subst; clear Heqatr.
  destruct tr; [by cbn; intro Ha0; apply Hpre; left |].
  rewrite last_cons.
  apply ForAllConsecutivePairsList_cons in Htr as [Ht Htr].
  intro Hlst; apply Hpre; right.
  exists i; split; [done |].
  by eapply IHatr.
Qed.
 
End sec_fix_points.
