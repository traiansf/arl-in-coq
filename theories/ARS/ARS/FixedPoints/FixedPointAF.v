From stdpp Require Import prelude.
From Coq Require Import ClassicalEpsilon.
From sets Require Import Ensemble.
From ARS Require Import Traces TransitionSystem CTL.

Section sec_fix_points.

Context
  `{TransitionSystem}
  (ψ : Ensemble idomain)
  .

Definition AF_ts_fixed_point_functor (X : Ensemble idomain) : Ensemble idomain :=
  fun a => a ∈ ψ \/ reducible a /\ forall b, transition a b -> b ∈ X.

Lemma AF_ts_pre_fixpoint :
  pre_fixpoint AF_ts_fixed_point_functor (AF_ts ψ).
Proof.
  intro a.
  intros [Ha | [Hnot_irreducible Hall]] tr Hhd Htr;
    [by subst; apply Exists_now |].
  inversion Htr as [? Hirreducible | ? ? Hfirst Hrest]; subst; [done |].
  by eapply Exists_delay, Hall.
Qed.

Lemma AF_ts_post_fixpoint :
  post_fixpoint AF_ts_fixed_point_functor (AF_ts ψ).
Proof.
  intros a Hall.
  unfold AF_ts_fixed_point_functor, elem_of, pow_set_elem_of.
  classical_right.
  split.
  - destruct (classic (reducible a)); [done |].
    specialize (Hall (Tnil a)).
    by feed specialize Hall; [| eapply complete_transition_chain_nil | inversion Hall].
  - intros b Hb tr <- Htr.
    specialize (Hall (Tcons a tr)).
    by feed specialize Hall; [| eapply complete_transition_chain_delay | inversion Hall].
Qed.

Lemma AF_ts_fixpoint :
  fixpoint AF_ts_fixed_point_functor (AF_ts ψ).
Proof.
  split.
  - apply (AF_ts_pre_fixpoint x).
  - apply (AF_ts_post_fixpoint x).
Qed.

Lemma not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint
  A (Hpre: pre_fixpoint AF_ts_fixed_point_functor A) :
  forall a, a ∉ A -> a ∉ ψ.
Proof.
  intros a Hna; contradict Hna; apply Hpre.
  by left.
Qed.

Lemma not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint_not_irreducible
  A (Hpre: pre_fixpoint AF_ts_fixed_point_functor A)
  (a: idomain)
  (Hna: a ∉ A)
  (Hnot_irreducible : ~ irreducible a)
  : exists a', a' ∉ A /\ transition a a'.
Proof.
  specialize (Hpre a).
   apply imply_to_or in Hpre as [Hpre |]; [| done].
  apply not_or_and in Hpre as [_ Hpre].
  apply not_and_or in Hpre as [| Hpre]; [done |].
  apply not_all_ex_not in Hpre as [a' Ha'].
  apply imply_to_and in Ha' as [].
  by exists a'.
Qed.

Section sec_iterated_choice.

Context
  (A : Ensemble idomain)
  (choose: {a : idomain | (a ∉ A) ∧ ¬ irreducible a} → idomain)
  (Hchoose_not_in: forall x : {a : idomain | (a ∉ A) ∧ ¬ irreducible a}, choose x ∉ A).

CoFixpoint iterated_choice
  (a : idomain)
  (Ha : a ∉ A)
  : trace idomain
  :=
  match (excluded_middle_informative (irreducible a)) with
  | left _ => Tnil a
  | right Hnot_irreducible =>
    Tcons a (iterated_choice _ (Hchoose_not_in (exist _ a (conj Ha Hnot_irreducible))))
  end.

Lemma iterated_choice_unfold
  (a : idomain)
  (Ha : a ∉ A)
  : iterated_choice a Ha
    =
    match (excluded_middle_informative (irreducible a)) with
    | left _ => Tnil a
    | right Hnot_irreducible =>
      Tcons a (iterated_choice _ (Hchoose_not_in (exist _ a (conj Ha Hnot_irreducible))))
    end.
Proof. by apply trace_eq_hd_tl; done. Qed.

Lemma iterated_choice_hd (a : idomain) (Ha : a ∉ A) :
  hd (iterated_choice a Ha) = a.
Proof.
  rewrite iterated_choice_unfold.
  by destruct (excluded_middle_informative (irreducible a)).
Qed.

End sec_iterated_choice.

Lemma AF_ts_least_pre_fixpoint A :
  pre_fixpoint AF_ts_fixed_point_functor A ->
  AF_ts ψ ⊆ A.
Proof.
  intros Hpre.
  unfold AF_ts.
  intro a; unfold elem_of at 1, pow_set_elem_of at 1; cbn.
  intros Hall.
  destruct (classic (a ∈ A)) as [| Hna]; [done |]; exfalso.
  cut (exists tr, hd tr = a /\ complete_transition_chain tr /\
      ForAll1 (fun b => b ∉ A) tr).
  {
    intros (tr & Hhd & Htr & Hall_b).
    specialize (Hall tr Hhd Htr).
    apply Exists1_exists in Hall as (n & Hn).
    contradict Hn.
    by eapply not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint, ForAll1_forall.
  }
  clear Hall.
  assert (Hall_ex :
   forall x : {a : idomain | a ∉ A /\ ~ irreducible a},
                    exists a' : idomain, (a' ∉ A) /\ transition (` x) a').
  {
    intros (a0 & Hna0 & Hnot_irreducible0).
    by apply not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint_not_irreducible.
  }
  apply choice in Hall_ex as [choose Hchoose].
  assert (Hchoose_not_in : forall x : {a : idomain | (a ∉ A) ∧ ¬ irreducible a},
    choose x ∉ A) by firstorder.
  exists (iterated_choice _ choose Hchoose_not_in _ Hna).
  repeat split.
  - by apply iterated_choice_hd.
  - unfold complete_transition_chain.
    revert a Hna.
    cofix CIH; intros a Hna.
    rewrite iterated_choice_unfold.
    destruct (excluded_middle_informative (irreducible a)) as [| Hnirreducible];
      [by apply Forall_nil |].
    apply Forall_delay.
    + rewrite iterated_choice_hd.
      change a with (` (exist (fun a => (a ∉ A) ∧ ¬ irreducible a) a (conj Hna Hnirreducible))).
      by apply Hchoose.
    + apply CIH.
  - revert a Hna.
    cofix CIH; intros a Hna.
    rewrite iterated_choice_unfold.
    destruct (excluded_middle_informative (irreducible a));
      [by apply Forall_nil |].
    apply Forall_delay; [done |].
    by apply CIH.
Qed.

End sec_fix_points.
