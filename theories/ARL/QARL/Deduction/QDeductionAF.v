From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARL Require Import TransitionSystem CTL RuleBasedTransitionSystem.
From ARL Require Import DeductionRules DeductionAF DeductionEF.

Record QuantifiedClaim `{TransitionSystem} {claim_quant : Type} := mk_qclaim
{
  claim_lhs : quantified_set claim_quant;
  claim_rhs : quantified_set claim_quant;
}.

Record Claim `{TransitionSystem} : Type := mk_claim
{
  claim_quant : Type;
  quantified_claim :> QuantifiedClaim (claim_quant := claim_quant)
}.

Definition quant_relation `{TransitionSystem} (R : relation (Ensemble idomain))
  (c : Claim) : Prop :=
  forall q : claim_quant c, R (claim_lhs c q) (claim_rhs c q).

Definition AF_rbts_claim `{TransitionSystem} (c : Claim) : Prop :=
  forall q : claim_quant c, AF_ts_claim (claim_lhs c q) (claim_rhs c q).

Definition EF_rbts_claim `{TransitionSystem} (c : Claim) : Prop :=
  forall q : claim_quant c, EF_ts_claim (claim_lhs c q) (claim_rhs c q).

Class QuantRuleOfReflexivity `{TransitionSystem} (P : Claim -> Prop) :=
  quant_rule_of_reflexivity : forall q (ϕ : quantified_set q),
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ; claim_rhs := ϕ |} |}.

Class QuantRuleOfTransitivity `{TransitionSystem} (P : Claim -> Prop) :=
  quant_rule_of_transitivity : forall q (ϕ ψ χ : quantified_set q),
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ; claim_rhs := ψ |} |} ->
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ψ; claim_rhs := χ |} |} ->
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ; claim_rhs := χ |} |}.

Class QuantRuleOfConsequence `{TransitionSystem} (P : Claim -> Prop) :=
  quant_rule_of_consequence : forall q (ϕ ψ ϕ' ψ' : quantified_set q),
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ; claim_rhs := ψ |} |} ->
    (forall (x : q), ϕ' x ⊆ ϕ x) -> (forall (x : q), ψ x ⊆ ψ' x) -> 
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ'; claim_rhs := ψ' |} |}.

Class QuantRuleOfDisjunction `{TransitionSystem} (P : Claim -> Prop) :=
  quant_rule_of_disjunction : forall q (ϕ1 ϕ2 ψ : quantified_set q),
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ1; claim_rhs := ψ |} |} ->
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ2; claim_rhs := ψ |} |} ->
    let ϕ := fun x : q => ϕ1 x ∪ ϕ2 x in
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ; claim_rhs := ψ |} |}.

Class QuantRuleOfGeneralization `{TransitionSystem} (P : Claim -> Prop) :=
  quant_rule_of_generalization : forall q `(ϕ : index -> quantified_set q) (ψ : quantified_set q),
    (forall i, P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ i; claim_rhs := ψ |} |}) ->
    let ϕ' := fun x => indexed_union (fun i => ϕ i x) in
    P {| claim_quant := q; quantified_claim := {| claim_lhs := ϕ'; claim_rhs := ψ |} |}.

(*
Class QuantRuleOfInduction `{TransitionSystem} (P : Claim -> Prop) :=
  quant_rule_of_induction :
    forall
      {qspace : Type}
      (prec : relation idomain)
      (Hwf : well_founded prec)
      {index}
      (φ : index -> quantified_set qspace)
      (ψ : index -> quantified_set qspace)
      (Hind )
*)
