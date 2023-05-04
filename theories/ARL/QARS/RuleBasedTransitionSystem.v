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

#[global] Instance ARLVarsEqProper : Proper ((≡) ==> (=) ==> (=) ==> (iff)) ARLVarsEq.
Proof.
  intros vars1 vars2 Hvars _v1 v1 -> _v2 v2 ->.
  apply set_equiv_subseteq in Hvars as [].
  by split; apply ARLVarsEqProper_subseteq.
Qed.

(** We say that a set of variables <<dependent_vars>> contains all the variables
that a pattern <<p>> depends on if for any two valuations which are
equal on <<dependent_vars>>, the valuations of the pattern using the two
valuations are equal.
*)
Definition pattern_dependent_vars (p : quantified_pattern) (dependent_vars : NameSet) : Prop :=
  forall (v1 v2 : Valuation Name), ARLVarsEq dependent_vars v1 v2 -> p v1 ≡ p v2.

Lemma pattern_dependent_varsProper_subseteq : Proper ((=) ==> (⊆) ==> (impl)) pattern_dependent_vars.
Proof.
  intros _p p -> vars1 vars2 Hvars Hvars1 v1 v2 Hvars2.
  apply Hvars1.
  revert Hvars2.
  by apply ARLVarsEqProper_subseteq.
Qed.

#[global] Instance pattern_dependent_varsProper : Proper ((=) ==> (≡) ==> (iff)) pattern_dependent_vars.
Proof.
  intros _p p -> vars1 vars2 Hequiv.
  apply set_equiv_subseteq in Hequiv as [].
  by split; apply pattern_dependent_varsProper_subseteq.
Qed.

Record ConstrainedTermStructure : Type :=
{
  ct_vars : NameSet;
  ct_term : quantified_term;
  ct_constraint : quantified_pattern;
}.

Record ConstrainedTermProps (ct : ConstrainedTermStructure) : Prop :=
{
  ct_term_vars : pattern_dependent_vars (ct_term ct) (ct_vars ct);
  ct_constraint_vars : pattern_dependent_vars (ct_constraint ct) (ct_vars ct);
  ct_constraint_predicate : arl_predicate (ct_constraint ct);
}.

Record ConstrainedTerm : Type :=
{
  ct :> ConstrainedTermStructure;
  ct_props : ConstrainedTermProps ct;
}.

Record RewriteRuleStructure : Type :=
{
  clhs : ConstrainedTermStructure;
  crhs : ConstrainedTermStructure;
}.

Record RewriteRuleProps (r : RewriteRuleStructure) : Prop :=
{
  lhs_props : ConstrainedTermProps (clhs r);
  rhs_props : ConstrainedTermProps (crhs r);
  vars_lhs_prop : ct_vars (clhs r) ⊆ ct_vars (crhs r);
}.

Record RewriteRule : Type :=
{
  rule :> RewriteRuleStructure;
  rule_props : RewriteRuleProps rule;
}.

Definition lhs (r : RewriteRuleStructure) : quantified_term := ct_term (clhs r).
Definition rhs (r : RewriteRuleStructure) : quantified_term := ct_term (crhs r).
Definition requires (r : RewriteRuleStructure) : quantified_pattern := ct_constraint (clhs r).
Definition ensures (r : RewriteRuleStructure) : quantified_pattern := ct_constraint (crhs r).
Definition vars (r : RewriteRuleStructure) : NameSet := ct_vars (crhs r).
Definition vars_lhs (r : RewriteRuleStructure) : NameSet := ct_vars (clhs r).

Record TransitionFromRuleInstance (r : RewriteRuleStructure) (v : Valuation Name) (a b : idomain) : Prop :=
{
  a_is_lhs : a = lhs r v;
  b_is_rhs : b = rhs r v;
  requires_holds : a ∈ requires r v;
  ensure_holds : b ∈ ensures r v;
}.

Definition transition_closed_to_rule_instance (r : RewriteRuleStructure) (v : Valuation Name) : Prop :=
  forall a b, TransitionFromRuleInstance r v a b -> transition a b.

Inductive TransitionFromRule (r : RewriteRuleStructure) (a b : idomain) : Prop :=
| tfr : forall v : Valuation Name, TransitionFromRuleInstance r v a b ->
  TransitionFromRule r a b.

Definition transition_rule_consistency (r : RewriteRuleStructure) : Prop :=
  forall v, lhs r v ∈ requires r v ->
    exists b, TransitionFromRule r (lhs r v) b.

Definition transition_closed_to_rule (r : RewriteRuleStructure) : Prop :=
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
  rules_consistent :
    set_Forall (fun r : RewriteRule NameSet => transition_rule_consistency NameSet r) rs;
}.

#[global] Hint Mode RuleBasedTransitionSystem - - - - - - - - - - - - - - - - - - - - - ! : typeclass_instances.

Arguments ct_vars {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope c : assert.

Arguments ct_term {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope c _ : assert.

Arguments ct_constraint {idomain}%type_scope {H} {NameSet}%type_scope
  {Name}%type_scope c _ _ : assert.

Arguments TransitionFromRuleInstance {idomain}%type_scope
  {H} {NameSet}%type_scope {Name}%type_scope r v a b : assert.

Arguments TransitionFromRule {idomain}%type_scope
  {H} {NameSet}%type_scope {Name}%type_scope r
  a b.

Arguments vars {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments vars_lhs {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments lhs {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments rhs {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments requires {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments ensures {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments clhs {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments crhs {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope r.

Arguments rule {idomain}%type_scope {H} {NameSet}%type_scope 
  {Name}%type_scope {H0} r.
