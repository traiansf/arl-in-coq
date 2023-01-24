From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARL.ARS Require Import TransitionSystem.

Definition Valuation `{TransitionSystem} (Name : Type) : Type := Name -> idomain.

Section sec_rule_based_transition_system.

Context
  `{TransitionSystem}
  (NameSet : Type)
  `{FinSet Name NameSet}.

Definition quantified_pattern : Type := Valuation Name -> Ensemble idomain.

Definition quantified_term : Type := Valuation Name -> idomain.

Definition quantified_term_to_pattern (t : quantified_term) : quantified_pattern :=
  fun v => {[ t v ]}.

#[global] Coercion quantified_term_to_pattern : quantified_term >-> quantified_pattern.

Definition arl_predicate `(p : quantified_pattern) : Prop :=
  forall v : Valuation Name, p v ≡ top idomain \/ p v ≡ ∅.

Definition quantified_variable (x : Name) : quantified_term :=
  fun v => v x.

Record ARLVarsEq (vars : NameSet) (v1 v2 : Valuation Name) :=
{
  arl_vars_eq : forall x, x ∈ vars -> v1 x = v2 x
}.

Lemma ARLVarsEqProper_subseteq : Proper ((⊆) --> (=) ==> (=) ==> (impl)) ARLVarsEq.
Proof.
  intros vars1 vars2 Hvars _v1 v1 -> _v2 v2 -> Hvars1.
  constructor; intros x Hx.
  by apply Hvars1, Hvars.
Qed.

#[global] Instance ARLVarsEqProper : Proper ((≡) --> (=) ==> (=) ==> (iff)) ARLVarsEq.
Proof.
  intros vars1 vars2 Hvars _v1 v1 -> _v2 v2 ->.
  apply set_equiv_subseteq in Hvars as [].
  by split; apply ARLVarsEqProper_subseteq.
Qed.

Definition pattern_dependent_vars (p : quantified_pattern) (dependent_vars : NameSet) : Prop :=
  forall (v1 v2 : Valuation Name), ARLVarsEq dependent_vars v1 v2 -> p v1 ≡ p v2.

Record RewriteRule : Type :=
{
  lhs : quantified_term;
  requires : quantified_pattern;
  rhs : quantified_term;
  ensures : quantified_pattern;
  vars : NameSet;
  vars_lhs : NameSet;
  vars_lhs_prop : vars_lhs ⊆ vars;
  lhs_vars : pattern_dependent_vars lhs vars_lhs;
  rhs_vars : pattern_dependent_vars rhs vars;
  requires_vars : pattern_dependent_vars requires vars_lhs;
  ensures_vars : pattern_dependent_vars ensures vars;
  requires_predicate : arl_predicate requires;
  ensures_predicate : arl_predicate ensures;
}.

Record TransitionFromRuleInstance (r : RewriteRule) (v : Valuation Name) (a b : idomain) : Prop :=
{
  a_is_lhs : a = lhs r v;
  b_is_rhs : b = rhs r v;
  requires_holds : a ∈ requires r v;
  ensure_holds : b ∈ ensures r v;
}.

Definition transition_closed_to_rule_instance (r : RewriteRule) (v : Valuation Name) : Prop :=
  forall a b, TransitionFromRuleInstance r v a b -> transition a b.

Inductive TransitionFromRule (r : RewriteRule) (a b : idomain) : Prop :=
| tfr : forall v : Valuation Name, TransitionFromRuleInstance r v a b ->
  TransitionFromRule r a b.

Definition transition_rule_consistency (r : RewriteRule) : Prop :=
  forall v, lhs r v ∈ requires r v ->
    exists b, TransitionFromRule r (lhs r v) b.

Definition transition_closed_to_rule (r : RewriteRule) : Prop :=
  forall a b, TransitionFromRule r a b -> transition a b.

Context
  `{Set_ RewriteRule RewriteRuleSet}.

Definition transition_from_rule_set (rs : RewriteRuleSet) (a b : idomain) : Prop :=
  set_Exists (fun r : RewriteRule => TransitionFromRule r a b) rs.

Definition transition_closed_to_rule_set (rs : RewriteRuleSet) : Prop :=
  forall a b, transition_from_rule_set rs a b -> transition a b.

Definition transition_included_in_rule_set (rs : RewriteRuleSet) : Prop :=
  forall a b, transition a b -> transition_from_rule_set rs a b.

End sec_rule_based_transition_system.

Class RuleBasedTransitionSystem
  `{TransitionSystem} (NameSet : Type) `{FinSet Name NameSet}
  `{Set_ (RewriteRule NameSet) RewriteRuleSet}
  (rs : RewriteRuleSet) :=
{
  rules_sound : transition_closed_to_rule_set NameSet rs;
  rules_complete : transition_included_in_rule_set NameSet rs;
  rules_consistent : set_Forall (transition_rule_consistency NameSet) rs;
}.

#[global] Hint Mode RuleBasedTransitionSystem - - - - - - - - - - - - - - - - - - - - - ! : typeclass_instances.

Arguments vars {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope {H0} r : assert.

Arguments vars_lhs {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope {H0} r : assert.

Arguments lhs {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope {H0} r _ : assert.

Arguments rhs {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope {H0} r _ : assert.

Arguments requires {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope {H0} r _ _ : assert.

Arguments ensures {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope {H0} r _ _ : assert.

Arguments TransitionFromRuleInstance {idomain}%type_scope
  {H} {NameSet}%type_scope {Name}%type_scope {H0} r v a b : assert.

Arguments TransitionFromRule {idomain}%type_scope
  {H} {NameSet}%type_scope {Name}%type_scope {H0} r
  a b.
