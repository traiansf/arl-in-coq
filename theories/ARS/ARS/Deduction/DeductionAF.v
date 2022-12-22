From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARS Require Import Traces TransitionSystem CTL.

Section sec_transition_system_deduction_rules.

Context `{TransitionSystem}.

Lemma rule_of_consequence φ φ' ψ ψ' :
  φ ⊆ φ' -> φ' ⊆ AF_ts ψ' -> ψ' ⊆ ψ ->
  φ ⊆ AF_ts ψ.
Proof.
  intros Hφ HAF Hψ.
  do 2 (etransitivity; [done |]).
  by rewrite Hψ.
Qed.

Lemma rule_of_reflexivity φ : φ ⊆ AF_ts φ.
Proof.
  intros a Ha tr <- _.
  by constructor 1.
Qed.

Lemma rule_of_transitivity φ χ ψ :
  φ ⊆ AF_ts χ ->
  χ ⊆ AF_ts ψ ->
  φ ⊆ AF_ts ψ.
Proof.
  intros Hφ Hχ.
  etransitivity; [done |].
  rewrite Hχ.
  by rewrite AF_ts_idempotent.
Qed.

Lemma rule_of_disjunction φ1 φ2 ψ :
  φ1 ⊆ AF_ts ψ ->
  φ2 ⊆ AF_ts ψ ->
  φ1 ∪ φ2 ⊆ AF_ts ψ.
Proof. by set_solver. Qed.

Lemma rule_of_generalization `(φ : qspace -> Ensemble idomain) ψ :
  (forall i, φ i ⊆ AF_ts ψ) ->
  indexed_union φ ⊆ AF_ts ψ.
Proof.
  intros Hall a; rewrite elem_of_indexed_union.
  intros [i Hai].
  by eapply Hall.
Qed.

Lemma rule_of_simple_step φ : φ ⊆ reducible ->
  φ ⊆ AF_ts (transition_image_functor φ).
Proof.
  intros Hred a Ha tr <- Htr.
  inversion Htr as [a Hirreducible| a tr' Ht _]; subst;
    [by unfold irreducible in Hirreducible; contradict Hirreducible; apply Hred |].
  apply Exists1_exists; exists 1.
  rewrite nth_keep_nil_cons.
  apply elem_of_filtered_union.
  eexists; split; [done |].
  by rewrite nth_keep_nil_0.
Qed.

Section sec_rule_of_induction.

Definition restrictR (R : relation idomain) (X : Ensemble idomain) : relation idomain :=
  fun a b => a ∈ X /\ b ∈ X /\ R a b.

Context
  `{qspace : Type} (* instances of quantifiers *)
  (measure : qspace -> idomain)
  (prec : relation idomain)
  (Hwf : well_founded prec)
  {index}
  (φ : index -> qspace -> Ensemble idomain)
  (ψ : index -> qspace -> Ensemble idomain)
  (Hind : forall q0,
    (forall q, prec (measure q) (measure q0) ->
      forall i, φ i q ⊆ AF_ts (ψ i q)) ->
    forall i, φ i q0 ⊆ AF_ts (ψ i q0))
  .

Lemma rule_of_induction :
    forall i q, φ i q ⊆ AF_ts (ψ i q).
Proof.
  pose (precQ := fun q1 q2 => prec (measure q1) (measure q2)).
  assert (HprecQ : well_founded precQ).
  {
    by apply wf_projected with prec measure.
  }
  intros.
  apply (well_founded_induction HprecQ
    (fun q => forall i, φ i q ⊆ AF_ts (ψ i q))).
  intros x Hind_x; apply Hind.
  by intros x0 Hx0; apply Hind_x.
Qed.

End sec_rule_of_induction.

End sec_transition_system_deduction_rules.
