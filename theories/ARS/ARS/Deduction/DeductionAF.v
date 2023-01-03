From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARS Require Import Traces TransitionSystem CTL.
From ARS Require Import DeductionRules.

Section sec_transition_system_deduction_rules.

Context `{TransitionSystem}.

Definition AF_ts_claim (ϕ ψ : Ensemble idomain) : Prop :=
  ϕ ⊆ AF_ts ψ.

#[export] Instance AF_rule_of_consequence : RuleOfConsequence AF_ts_claim.
Proof.
  intros φ' φ Hφ ψ' ψ Hψ HAF; unfold AF_ts_claim.
  do 2 (etransitivity; [done |]).
  by rewrite Hψ.
Qed.

#[export] Instance AF_rule_of_reflexivity : Reflexive AF_ts_claim.
Proof.
  intros ϕ a Ha tr <- _.
  by constructor 1.
Qed.

#[export] Instance AF_rule_of_transitivity : Transitive AF_ts_claim.
Proof.
  unfold AF_ts_claim; intros φ χ ψ Hφ Hχ.
  etransitivity; [done |].
  rewrite Hχ.
  by rewrite AF_ts_idempotent.
Qed.

#[export] Instance AF_rule_of_disjunction : RuleOfDisjunction AF_ts_claim.
Proof.
  by intros φ1 φ2 ψ; unfold AF_ts_claim; set_solver.
Qed.

#[export] Instance AF_rule_of_generalization : RuleOfGeneralization AF_ts_claim.
Proof.
  intros ? φ ψ Hall a; rewrite elem_of_indexed_union.
  intros [i Hai].
  by eapply Hall.
Qed.

#[export] Instance AF_rule_of_all_paths_single_step : RuleOfAllPathsSingleStep AF_ts_claim.
Proof.
  intros ? Hred ** a Ha tr <- Htr.
  inversion Htr as [a Hirreducible| a tr' Ht _]; subst;
    [by unfold irreducible in Hirreducible; contradict Hirreducible; apply Hred |].
  apply Exists1_exists; exists 1.
  rewrite nth_keep_nil_cons.
  apply elem_of_filtered_union.
  eexists; split; [done |].
  by rewrite nth_keep_nil_0.
Qed.

#[export] Instance AF_rule_of_induction : RuleOfInduction AF_ts_claim.
Proof.
  intros ? **.
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

#[export] Instance AF_all_path_deduction : AllPathsAFDeduction AF_ts_claim.
Proof. Qed.

End sec_transition_system_deduction_rules.
