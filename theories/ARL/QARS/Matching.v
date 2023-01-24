From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From sets Require Import Ensemble.
From ARL Require Import TransitionSystem RuleBasedTransitionSystem.

Definition substitution `{TransitionSystem} (Name : Type) : Type := Name -> quantified_term (Name := Name).

Section sec_matching.

Context
  `{TransitionSystem}
  (NameSet : Type)
  `{FinSet Name NameSet}.

Definition substitution_dependent_vars
  (s : substitution Name) (interesting_vars dependent_vars : NameSet) : Prop :=
  set_Forall (fun x => pattern_dependent_vars NameSet (s x) dependent_vars) interesting_vars.

Definition substitute_term (s : substitution Name) (t : quantified_term) : quantified_term :=
  fun v => t (fun x => s x v).

Definition substitute_pattern (s : substitution Name) (p : quantified_pattern) : quantified_pattern :=
  fun v => p (fun x => s x v).

Lemma substitute_term_dependent_vars s (t : quantified_term) t_vars s_vars :
  pattern_dependent_vars NameSet t t_vars ->
  substitution_dependent_vars s t_vars s_vars ->
  pattern_dependent_vars NameSet (substitute_term s t) s_vars.
Proof.
  intros Ht_deps Hs_deps v1 v2 Heqvars.
  apply Ht_deps.
  constructor; intros x Hx.
  by apply (Hs_deps x Hx _ _ Heqvars).
Qed.

Lemma substitute_pattern_dependent_vars s (t : quantified_pattern) t_vars s_vars :
  pattern_dependent_vars NameSet t t_vars ->
  substitution_dependent_vars s t_vars s_vars ->
  pattern_dependent_vars NameSet (substitute_pattern s t) s_vars.
Proof.
  intros Ht_deps Hs_deps v1 v2 Heqvars.
  apply Ht_deps.
  constructor; intros x Hx.
  by apply (Hs_deps x Hx _ _ Heqvars).
Qed.

Record Substitution :=
{
  sub :> substitution Name;
  sub_from : NameSet;
  sub_to : NameSet;
  sub_dep_vars : substitution_dependent_vars sub sub_from sub_to;
  sub_free_vars : forall x, x ∉ sub_from -> sub x = quantified_variable x;
}.

Lemma Substitute_term_dependent_vars s (t : quantified_term):
  pattern_dependent_vars NameSet t (sub_from s) ->
  pattern_dependent_vars NameSet (substitute_term s t) (sub_to s).
Proof.
  intros.
  by eapply substitute_term_dependent_vars, s.
Qed.

Lemma Substitute_pattern_dependent_vars s (t : quantified_pattern):
  pattern_dependent_vars NameSet t (sub_from s) ->
  pattern_dependent_vars NameSet (substitute_pattern s t) (sub_to s).
Proof.
  intros.
  by eapply substitute_pattern_dependent_vars, s.
Qed.

