From stdpp Require Import prelude fin_maps.
From Coq Require Import FunctionalExtensionality Classical.
From sets Require Import Ensemble.
From ARL Require Import FreshExtras.
From ARL Require Import TransitionSystem RuleBasedTransitionSystem.

Section sec_refresh_rule.

Context
  `{TransitionSystem}
  (NameSet : Type)
  `{FinSet Name NameSet}.

Definition valuationXchange
  (v : Valuation Name) (to_replace replacement : Name) : Valuation Name :=
  fun (x : Name) =>
    if (decide (x = to_replace)) then v replacement
    else if (decide (x = replacement)) then v to_replace
    else v x.

Lemma valuationXchange_left v x y : valuationXchange v x y x = v y.
Proof. by unfold valuationXchange; case_decide. Qed.

Lemma valuationXchange_right v x y : valuationXchange v x y y = v x.
Proof. by unfold valuationXchange; case_decide; [subst | rewrite decide_True]. Qed.

Lemma valuationXchange_other v x y z :
  z <> x -> z <> y -> valuationXchange v x y z = v z.
Proof. by intros; unfold valuationXchange; rewrite !decide_False. Qed.

Definition valuationXchange_iter
  (v : Valuation Name) (subst : list (Name * Name)) : Valuation Name :=
    foldr (fun xy (p : Valuation Name) => valuationXchange p xy.1 xy.2) v subst.

Lemma valuationXchange_iter_other
  (subst : list (Name * Name)) (to_replace := map fst subst) (replacement := map snd subst) :
  forall x, x ∉ to_replace -> x ∉ replacement ->
  forall v, valuationXchange_iter v subst x = v x.
Proof.
  unfold valuationXchange_iter; induction subst; [done |].
  subst to_replace replacement; cbn.
  intro x; rewrite !not_elem_of_cons; intros [Hna1 Hnx1] [Hna2 Hnx2] v.
  unfold valuationXchange at 1.
  rewrite !decide_False by done.
  by apply IHsubst.
Qed.

Lemma valuationXchange_iter_replaced
  (subst : list (Name * Name)) (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  forall xy, xy ∈ subst ->
  forall v, valuationXchange_iter v subst xy.1 = v xy.2 /\ valuationXchange_iter v subst xy.2 = v xy.1.
Proof.
  induction subst; [by inversion 2 |].
  rewrite NoDup_app; subst to_replace replacement; cbn.
  rewrite !NoDup_cons; intros ([Hna1 Hnodup1] & Hdisj' & Hna2 & Hnodup2) xy.
  assert (Hna1' : a.1 ∉ map snd subst)
    by (intros Ha1; apply (Hdisj' a.1); [left | right]; done).
  assert (Hna2' : a.2 ∉ map fst subst)
    by (intros Ha2; apply (Hdisj' a.2); [right | left]; done).
  assert (Hna12 : a.1 <> a.2)
    by (intros Heq; rewrite Heq in Hdisj'; apply (Hdisj' a.2); left).
  assert (Hdisj : forall x, x ∈ map fst subst -> x ∉ map snd subst)
    by (intros x Hx1 Hx2; apply (Hdisj' x); right; done).
  rewrite elem_of_cons; intros [-> | Hxy].
  - split; unfold valuationXchange at 1.
    + rewrite decide_True by done.
      by apply valuationXchange_iter_other.
    + rewrite decide_False, decide_True by done.
      by apply valuationXchange_iter_other.
  - rewrite elem_of_list_fmap in Hna1, Hna2, Hna1', Hna2'.
    intro v; rewrite !valuationXchange_other.
    + by apply IHsubst; [apply NoDup_app |].
    + by contradict Hna1'; eexists.
    + by contradict Hna2; eexists.
    + by contradict Hna1; eexists.
    + by contradict Hna2'; eexists.
Qed.

Lemma valuationXchange_iter_left
  (subst : list (Name * Name)) (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  forall xy, xy ∈ subst ->
  forall v, valuationXchange_iter v subst xy.1 = v xy.2.
Proof. by intros; apply valuationXchange_iter_replaced. Qed.

Lemma valuationXchange_iter_right
  (subst : list (Name * Name)) (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  forall xy, xy ∈ subst ->
  forall v, valuationXchange_iter v subst xy.2 = v xy.1.
Proof. by intros; apply valuationXchange_iter_replaced. Qed.

Lemma valuationXchange_iter_twice
  (subst : list (Name * Name)) (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  forall v, valuationXchange_iter (valuationXchange_iter v subst) subst = v.
Proof.
  intros Hnodup v.
  extensionality x.
  destruct (decide (x ∈ to_replace ++ replacement)) as [Hin | Hnin];
    [apply elem_of_app in Hin as [Hin | Hin] |].
  - apply elem_of_list_fmap in Hin as (xy & -> & Hxy).
    by rewrite valuationXchange_iter_left, valuationXchange_iter_right.
  - apply elem_of_list_fmap in Hin as (xy & -> & Hxy).
    by rewrite valuationXchange_iter_right, valuationXchange_iter_left.
  - apply not_elem_of_app in Hnin as [].
    by etransitivity; apply valuationXchange_iter_other.
Qed.

Definition qpattern_rename_vars_with
  (p : quantified_pattern) (subst : list (Name * Name)) : quantified_pattern :=
  fun v => p (valuationXchange_iter v subst).

Definition qterm_rename_vars_with
  (p : quantified_term) (subst : list (Name * Name)) : quantified_term :=
  fun v => p (valuationXchange_iter v subst).

Lemma qterm_rename_vars_with_valuation p subst v :
  qterm_rename_vars_with p subst v
    =
  p (valuationXchange_iter v subst).
Proof. done. Qed.

Existing Instance elem_of_dec_slow.

Lemma arl_vars_eq_rename_iter_sub subst v1 v2
  (to_replace := map fst subst) (replacement := map snd subst)
  (to_replace_set : NameSet := list_to_set to_replace)
  (replacement_set : NameSet := list_to_set replacement) :
  NoDup (to_replace ++ replacement) ->
  forall (vars_to_replace : NameSet)
    (vars_replacement := list_to_set (map snd (filter (fun xy => xy.1 ∈ vars_to_replace) subst))),
    vars_to_replace ⊆ to_replace_set ->
  ARLVarsEq NameSet vars_replacement v1 v2 ->
  ARLVarsEq NameSet vars_to_replace
    (valuationXchange_iter v1 subst)
    (valuationXchange_iter v2 subst).
Proof.
  intros Hnodup ? ? Hincl Heq.
  constructor; intros x Hx.
  apply Hincl in Hx as Hx'.
  apply elem_of_list_to_set, elem_of_list_fmap in Hx' as (xy & -> & Hxy).
  rewrite !valuationXchange_iter_left by done.
  apply Heq, elem_of_list_to_set, elem_of_list_fmap.
  by eexists; rewrite elem_of_list_filter.
Qed.

Lemma arl_vars_eq_rename_iter subst v1 v2
  (to_replace := map fst subst) (replacement := map snd subst)
  (to_replace_set : NameSet := list_to_set to_replace)
  (replacement_set : NameSet := list_to_set replacement) :
  NoDup (to_replace ++ replacement) ->
  ARLVarsEq NameSet replacement_set v1 v2 ->
  ARLVarsEq NameSet to_replace_set
    (valuationXchange_iter v1 subst)
    (valuationXchange_iter v2 subst).
Proof.
  intros Hnodup Heq.
  constructor; intros x Hx.
  apply elem_of_list_to_set, elem_of_list_fmap in Hx as (xy & -> & Hxy).
  rewrite !valuationXchange_iter_left by done.
  apply Heq, elem_of_list_to_set, elem_of_list_fmap.
  by eexists.
Qed.

Lemma pattern_dependent_vars_rename_pattern_sub p vars1 subst
  (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  pattern_dependent_vars NameSet p vars1 ->
  vars1 ⊆ list_to_set to_replace ->
  let vars2 := list_to_set (map snd (filter (fun xy => xy.1 ∈ vars1) subst)) in
  pattern_dependent_vars NameSet (qpattern_rename_vars_with p subst) vars2.
Proof.
  intros Hnodup Hdep Hinc vars2 v1 v2 Heq.
  by apply Hdep, arl_vars_eq_rename_iter_sub.
Qed.

Lemma pattern_dependent_vars_rename_pattern p subst
  (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  pattern_dependent_vars NameSet p (list_to_set to_replace) ->
  pattern_dependent_vars NameSet (qpattern_rename_vars_with p subst) (list_to_set replacement).
Proof.
  intros Hnodup Hdep v1 v2 Heq.
  by apply Hdep, arl_vars_eq_rename_iter.
Qed.

Lemma pattern_dependent_vars_rename_term_sub (p : quantified_term) vars1 subst
  (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  pattern_dependent_vars NameSet p vars1 ->
  vars1 ⊆ list_to_set to_replace ->
  let vars2 := list_to_set (map snd (filter (fun xy => xy.1 ∈ vars1) subst)) in
  pattern_dependent_vars NameSet (qterm_rename_vars_with p subst) vars2.
Proof.
  intros Hnodup Hdep Hinc vars2 v1 v2 Heq.
  by apply Hdep, arl_vars_eq_rename_iter_sub.
Qed.

Lemma pattern_dependent_vars_rename_term (p : quantified_term) subst
  (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  pattern_dependent_vars NameSet p (list_to_set to_replace) ->
  pattern_dependent_vars NameSet (qterm_rename_vars_with p subst) (list_to_set replacement).
Proof.
  intros Hnodup Hdep v1 v2 Heq.
  by apply Hdep, arl_vars_eq_rename_iter.
Qed.

Lemma qterm_rename_vars_with_valuation_rev (p : quantified_term) subst
  (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  forall v, p v = qterm_rename_vars_with p subst (valuationXchange_iter v subst).
Proof.
  unfold qterm_rename_vars_with.
  by intros; rewrite valuationXchange_iter_twice.
Qed.

Lemma qpattern_rename_vars_with_valuation_rev p subst
  (to_replace := map fst subst) (replacement := map snd subst) :
  NoDup (to_replace ++ replacement) ->
  forall v, p v = qpattern_rename_vars_with p subst (valuationXchange_iter v subst).
Proof.
  unfold qpattern_rename_vars_with.
  by intros; rewrite valuationXchange_iter_twice.
Qed.

Definition constrained_term_structure_rename_vars_with
  (ct : ConstrainedTermStructure NameSet) (subst : list (Name * Name))
  : ConstrainedTermStructure NameSet :=
  let subst_vars := filter (fun xy => xy.1 ∈ ct_vars ct) subst in
  {|
    ct_vars := list_to_set (map snd subst_vars) ;
    ct_term := qterm_rename_vars_with (ct_term ct) subst ;
    ct_constraint := qpattern_rename_vars_with (ct_constraint ct) subst ;
  |}.

Context
  `{Infinite Name}.

Lemma constrained_term_props_rename_vars_with
  (ct : ConstrainedTermStructure NameSet) 
  (avoid : NameSet) :
  forall vars (subst := refresh_list vars avoid),
  ct_vars ct ⊆ vars ->
  ConstrainedTermProps NameSet ct -> 
  ConstrainedTermProps NameSet
    (constrained_term_structure_rename_vars_with ct subst).
Proof.
  intros vars subst Hincl Hct; subst subst.
  constructor; cbn.
  - apply pattern_dependent_vars_rename_term_sub;
      [by apply refresh_list_nodup | by apply Hct |..].
    by rewrite refresh_list_fst, list_to_set_elements.
  - apply pattern_dependent_vars_rename_pattern_sub;
      [by apply refresh_list_nodup | by apply Hct |..].
    by rewrite refresh_list_fst, list_to_set_elements.
  - by intro; apply Hct.
Qed.

Definition rewrite_rule_structure_rename_vars_with
  (r : RewriteRuleStructure NameSet) (subst : list (Name * Name))
  : RewriteRuleStructure NameSet :=
  {|
    clhs := constrained_term_structure_rename_vars_with (clhs r) subst;
    crhs := constrained_term_structure_rename_vars_with (crhs r) subst;
  |}.

Program Definition rewrite_rule_refresh_vars (r : RewriteRule NameSet) (avoid : NameSet) : RewriteRule NameSet :=
  let subst := refresh_list (vars r) avoid in
  {|
    rule := rewrite_rule_structure_rename_vars_with (rule r) subst;
  |}.
Next Obligation.
  constructor.
  - by apply constrained_term_props_rename_vars_with; apply r.
  - by apply constrained_term_props_rename_vars_with, r.
  - cbn; intro y; rewrite !elem_of_list_to_set, !elem_of_list_fmap.
    setoid_rewrite elem_of_list_filter.
    intros (xy & -> & Hx & Hxy).
    by eexists; split_and!; [| apply r |].
Qed.

Lemma rewrite_rule_refresh_vars_disj r avoid :
  vars (rewrite_rule_refresh_vars r avoid) ## (avoid ∪ vars r).
Proof.
  cbn; intro x; rewrite elem_of_union; intros ? [].
  - by eapply @refresh_list_replacements_avoid with (KSet := NameSet).
  - by eapply @refresh_list_replacements_orig with (KSet := NameSet).
Qed.

Lemma rewrite_rule_refresh_vars_disj_original r avoid :
  vars (rewrite_rule_refresh_vars r avoid) ## vars r.
Proof. by apply refresh_list_replacements_orig. Qed.

Lemma rewrite_rule_refresh_vars_disj_avoid r avoid :
  vars (rewrite_rule_refresh_vars r avoid) ## avoid.
Proof. by apply refresh_list_replacements_avoid. Qed.

#[local] Lemma TransitionFromRuleInstance_refresh_vars r avoid
  (refreshed := rewrite_rule_refresh_vars r avoid)
  (subst := refresh_list (vars r) avoid)
  (v : Valuation Name)
  (a b : idomain) :
  TransitionFromRuleInstance r v a b
    ->
  TransitionFromRuleInstance refreshed (valuationXchange_iter v subst) a b.
Proof.
  pose proof (Hnodup := refresh_list_nodup (vars r) avoid).
  intros []; constructor; cbn.
  - by rewrite <- qterm_rename_vars_with_valuation_rev.
  - by rewrite <- qterm_rename_vars_with_valuation_rev.
  - by rewrite <- qpattern_rename_vars_with_valuation_rev.
  - by rewrite <- qpattern_rename_vars_with_valuation_rev.
Qed.

#[local] Lemma TransitionFromRuleInstance_refresh_vars_rev r avoid
  (refreshed := rewrite_rule_refresh_vars r avoid)
  (subst := refresh_list (vars r) avoid)
  (v : Valuation Name)
  (a b : idomain) :
  TransitionFromRuleInstance refreshed v a b
    ->
  TransitionFromRuleInstance r (valuationXchange_iter v subst) a b.
Proof. by intros []; constructor. Qed.

Lemma TransitionFromRule_refresh_vars (r : RewriteRule NameSet) avoid :
  forall a b, TransitionFromRule r a b <->
    TransitionFromRule (rewrite_rule_refresh_vars r avoid) a b.
Proof.
  intros; split; intros []; econstructor.
  - by apply TransitionFromRuleInstance_refresh_vars.
  - by apply TransitionFromRuleInstance_refresh_vars_rev.
Qed.

End sec_refresh_rule.
