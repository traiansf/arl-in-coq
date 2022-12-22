From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARS.ARS Require Import TransitionSystem.

Section sec_rule_based_transition_system.

Definition quantified_set `{TransitionSystem} (quant : Type) : Type := quant -> Ensemble idomain.
Definition quantified_element `{TransitionSystem} (quant : Type) : Type := quant -> idomain.

Record RewriteRule `{TransitionSystem} : Type :=
{
  quant : Type;
  lhs : quantified_set quant;
  rhs : quantified_element quant
}.

Record Claim `{TransitionSystem} : Type :=
{
  af_quant : Type;
  af_lhs : quantified_set af_quant;
  af_rhs : quantified_set af_quant;
}.

Context `{TransitionSystem}.

Record TransitionFromRuleInstance (r : RewriteRule) (q : quant r) (a b : idomain) : Prop :=
{
  a_in_lhs : a ∈ lhs r q;
  b_is_rhs : b = rhs r q;
}.

Definition transition_closed_to_rule_instance (r : RewriteRule) (q : quant r) : Prop :=
  forall a b, TransitionFromRuleInstance r q a b -> transition a b.

Inductive TransitionFromRule (r : RewriteRule) (a b : idomain) : Prop :=
| tfr : forall q : quant r, TransitionFromRuleInstance r q a b ->
  TransitionFromRule r a b.

Definition transition_closed_to_rule (r : RewriteRule) : Prop :=
  forall a b, TransitionFromRule r a b -> transition a b.

Definition transition_from_rule_set
  `{Set_ RewriteRule RewriteRuleSet} (rs : RewriteRuleSet)
  (a b : idomain) : Prop :=
  set_Exists (fun r => TransitionFromRule r a b) rs.

Definition transition_closed_to_rule_set
  `{Set_ RewriteRule RewriteRuleSet} (rs : RewriteRuleSet) : Prop :=
  forall a b, transition_from_rule_set rs a b -> transition a b.

Definition transition_included_in_rule_set
  `{Set_ RewriteRule RewriteRuleSet} (rs : RewriteRuleSet) : Prop :=
  forall a b, transition a b -> transition_from_rule_set rs a b.

Definition AF_satisfies (c : Claim) : Prop :=
  forall q : af_quant c, af_lhs c q ⊆ AF_ts (af_rhs c q).

End sec_rule_based_transition_system.

Class RuleBasedTransitionSystem
  `{TransitionSystem} `{Set_ RewriteRule RewriteRuleSet}
  (rs : RewriteRuleSet) :=
{
  rules_sound : transition_closed_to_rule_set rs;
  rules_complete : transition_included_in_rule_set rs;
}.

#[global] Hint Mode RuleBasedTransitionSystem - - - - - - - - - - ! : typeclass_instances.
