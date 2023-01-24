From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARL Require Import Traces TransitionSystem CTL.
From ARL Require Import DeductionRules.

Section sec_transition_system_deduction_rules.

Context `{TransitionSystem}.

Definition EF_ts_claim (ϕ ψ : Ensemble idomain) : Prop :=
  ϕ ⊆ EF_ts ψ.

#[export] Instance EF_rule_of_consequence : RuleOfConsequence EF_ts_claim.
Proof.
  intros φ' φ Hφ ψ' ψ Hψ HAF; unfold EF_ts_claim.
  do 2 (etransitivity; [done |]).
  by rewrite Hψ.
Qed.

#[export] Instance EF_rule_of_reflexivity : Reflexive EF_ts_claim.
Proof.
  intros ϕ a Ha.
  by exists []; split; [repeat constructor |].
Qed.

#[export] Instance EF_rule_of_transitivity : Transitive EF_ts_claim.
Proof.
  unfold EF_ts_claim; intros φ χ ψ Hφ Hχ.
  etransitivity; [done |].
  rewrite Hχ.
  by rewrite EF_ts_idempotent.
Qed.

#[export] Instance EF_rule_of_disjunction : RuleOfDisjunction EF_ts_claim.
Proof.
  by intros φ1 φ2 ψ; unfold EF_ts_claim; set_solver.
Qed.

#[export] Instance EF_rule_of_generalization : RuleOfGeneralization EF_ts_claim.
Proof.
  intros ? φ ψ Hall a; rewrite elem_of_indexed_union.
  intros [i Hai].
  by eapply Hall.
Qed.

#[export] Instance EF_rule_of_one_path_single_step : RuleOfOnePathSingleStep EF_ts_claim.
Proof.
  intros ? ? Hred a Ha.
  destruct (Hred a Ha) as (b & Hb & Ht).
  exists [b]; split; [| done].
  by repeat constructor.
Qed.

#[export] Instance EF_rule_of_induction : RuleOfInduction EF_ts_claim.
Proof.
  intros ? **.
  pose (precQ := fun q1 q2 => prec (measure q1) (measure q2)).
  assert (HprecQ : well_founded precQ).
  {
    by apply wf_projected with prec measure.
  }
  intros.
  apply (well_founded_induction HprecQ
    (fun q => forall i, φ i q ⊆ EF_ts (ψ i q))).
  intros x Hind_x; apply Hind.
  by intros x0 Hx0; apply Hind_x.
Qed.

#[export] Instance EF_all_path_deduction : OnePathEFDeduction EF_ts_claim.
Proof. Qed.

End sec_transition_system_deduction_rules.
