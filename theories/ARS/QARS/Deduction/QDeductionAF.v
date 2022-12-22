From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARS Require Import TransitionSystem CTL RuleBasedTransitionSystem.


Record Claim `{TransitionSystem} : Type :=
{
  af_quant : Type;
  af_lhs : quantified_set af_quant;
  af_rhs : quantified_set af_quant;
}.

Definition AF_satisfies `{TransitionSystem} (c : Claim) : Prop :=
  forall q : af_quant c, af_lhs c q ⊆ AF_ts (af_rhs c q).
