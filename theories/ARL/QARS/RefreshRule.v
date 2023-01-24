From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From sets Require Import Ensemble.
From ARL Require Import TransitionSystem RuleBasedTransitionSystem.

Definition find_position `{EqDecision A} (l : list A) (a : A) : option nat :=
  fst <$> list_find (fun x => x = a) l.

Lemma find_position_Some `{EqDecision A} (l : list A) a n :
  find_position l a = Some n -> l !! n = Some a.
Proof.
  unfold find_position; intro Hpos.
  destruct list_find as [(_n, _a) |] eqn: Hlist_find_eq; [| by inversion Hlist_find_eq].
  apply Some_inj in Hpos; subst n.
  by apply list_find_Some in Hlist_find_eq as (? & -> & _).
Qed.

Lemma find_position_elem_of `{EqDecision A} (l : list A) a :
  a ∈ l <-> is_Some (find_position l a).
Proof.
  split.
  - intro Ha.
    cut (is_Some (list_find (fun x => x = a) l)).
    {
      intros [(_a, n) H_a].
      by exists _a; unfold find_position; rewrite H_a.
    }
    by eapply list_find_elem_of.
  - intros [n Hn].
    by apply find_position_Some, elem_of_list_lookup_2 in Hn.
Qed.

Lemma find_position_None `{EqDecision A} (l : list A) a :
  find_position l a = None <-> a ∉ l.
Proof.
  rewrite find_position_elem_of.
  by apply eq_None_not_Some.
Qed.

Definition find_positions `{EqDecision A} (l subl : list A) : list nat :=
  omap (find_position l) subl.

Lemma find_positions_elem_of `{EqDecision A} (l subl : list A) x :
  subl ⊆ l ->
  x ∈ subl ->
  x ∈ l <-> exists i, i ∈ find_positions l subl /\ l !! i = Some x.
Proof.
  induction subl; [by inversion 2 |].
  intros Hincl.
  inversion 1; subst.
  - rewrite find_position_elem_of; split.
    + intros [i Hi]; exists i.
      split; [| by apply find_position_Some].
      unfold find_positions; rewrite elem_of_list_omap.
      by exists a; split; [left |].
    + intros (i & Hi & Hlookup).
      apply find_position_elem_of, elem_of_list_lookup.
      by eexists.
  - rewrite IHsubl; [| by set_solver | done].
    apply exist_proper; intro i.
    unfold find_positions; rewrite !elem_of_list_omap.
    split; intros [(_x & H_x & Hpos) Hi]; (split; [| done]); exists _x; (split; [| done]).
    + by right.
    + apply find_position_Some in Hpos.
      rewrite Hpos in Hi.
      by congruence.
Qed.

Definition multiple_lookups `(l : list A) (positions : list nat) : list A :=
  omap (fun i => lookup i l) positions.

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
  (v : Valuation Name) (to_replace replacement : list Name) : Valuation Name :=
    foldr (fun (xy : Name * Name) (p : Valuation Name) => valuationXchange p xy.1 xy.2)
      v (zip to_replace replacement).

Lemma valuationXchange_iter_cons v x xs y ys :
  valuationXchange_iter v (x :: xs) (y :: ys)
    =
  valuationXchange (valuationXchange_iter v xs ys) x y.
Proof. done. Qed.

Lemma valuationXchange_iter_other v to_replace replacement :
  forall x, x ∉ to_replace -> x ∉ replacement ->
  valuationXchange_iter v to_replace replacement x = v x.
Proof.
  revert v replacement; induction to_replace; [done |].
  intros v replacement x Hx1 Hx2.
  apply not_elem_of_cons in Hx1 as [Hxa Hx1].
  destruct replacement as [| r replacement]; [done |].
  apply not_elem_of_cons in Hx2 as [Hxr Hx2].
  rewrite valuationXchange_iter_cons, valuationXchange_other by done.
  by apply IHto_replace.
Qed.

Lemma valuationXchange_iter_replaced v to_replace replacement :
  NoDup to_replace ->
  NoDup replacement ->
  (forall x, x ∈ to_replace -> x ∈ replacement -> False) ->
  forall n,
  forall x, to_replace !! n = Some x ->
  forall y, replacement !! n = Some y ->
  valuationXchange_iter v to_replace replacement x = v y
    /\
  valuationXchange_iter v to_replace replacement y = v x.
Proof.
  revert replacement; induction to_replace; [done |].
  intros replacement Hnodup1 Hnodup2 Hdisj n x Hx y Hy.
  destruct replacement as [| b]; [by inversion Hy |].
  rewrite valuationXchange_iter_cons.
  apply NoDup_cons in Hnodup1 as [Ha Hnodup1].
  apply NoDup_cons in Hnodup2 as [Hb Hnodup2].
  destruct n.
  - inversion Hx; inversion Hy; subst; clear Hx Hy.
    rewrite valuationXchange_left, valuationXchange_right.
    split; apply valuationXchange_iter_other; [| done | done |].
    + by intro Hy; eapply Hdisj; [right | left].
    + by intro Hx; eapply Hdisj; [left | right].
  - cbn in Hx, Hy.
    rewrite !valuationXchange_other; cycle 1.
    + intros ->; eapply Hdisj; [by left |]; right.
      by apply elem_of_list_lookup; eexists.
    + by contradict Hb; subst; apply elem_of_list_lookup; eexists.
    + by contradict Ha; subst; apply elem_of_list_lookup; eexists.
    + intros ->; eapply Hdisj; [| by left]; right.
      by apply elem_of_list_lookup; eexists.
    + eapply IHto_replace; [done | done | | done..].
      by intros; eapply Hdisj; right.
Qed.

Lemma valuationXchange_iter_left v to_replace replacement :
  NoDup to_replace ->
  NoDup replacement ->
  (forall x, x ∈ to_replace -> x ∈ replacement -> False) ->
  forall n,
  forall x, to_replace !! n = Some x ->
  forall y, replacement !! n = Some y ->
  valuationXchange_iter v to_replace replacement x = v y.
Proof.
  by intros; eapply valuationXchange_iter_replaced with (x := x).
Qed.

Lemma valuationXchange_iter_right v to_replace replacement :
  NoDup to_replace ->
  NoDup replacement ->
  (forall x, x ∈ to_replace -> x ∈ replacement -> False) ->
  forall n,
  forall x, to_replace !! n = Some x ->
  forall y, replacement !! n = Some y ->
  valuationXchange_iter v to_replace replacement y = v x.
Proof.
  by intros; eapply valuationXchange_iter_replaced with (x := x).
Qed.

Lemma valuationXchange_iter_twice v to_replace replacement :
  NoDup to_replace ->
  NoDup replacement ->
  (forall x, x ∈ to_replace -> x ∈ replacement -> False) ->
  length to_replace = length replacement ->
  valuationXchange_iter (valuationXchange_iter v to_replace replacement)
    to_replace replacement = v.
Proof.
  intros Hnodup1 Hnodup2 Hdisj Hlength.
  extensionality x.
  destruct (decide (x ∈ to_replace)) as [Hx | Hnx];
    [| destruct (decide (x ∈ replacement)) as [Hx' | Hnx']].
  - apply elem_of_list_lookup in Hx as [n Hx].
    apply lookup_lt_Some in Hx as Hn.
    rewrite Hlength in Hn.
    apply lookup_lt_is_Some in Hn as [y Hy].
    rewrite valuationXchange_iter_left with (n := n) (y := y) by done.
    by rewrite valuationXchange_iter_right with (n := n) (x := x).
  - apply elem_of_list_lookup in Hx' as [n Hx'].
    apply lookup_lt_Some in Hx' as Hn.
    rewrite <- Hlength in Hn.
    apply lookup_lt_is_Some in Hn as [y Hy].
    rewrite valuationXchange_iter_right with (n := n) (x := y) by done.
    by rewrite valuationXchange_iter_left with (n := n) (y := x).
  - by rewrite !valuationXchange_iter_other.
Qed.

Definition qpattern_rename_vars_with
  (p : quantified_pattern) (to_rename renaming : list Name)
  : quantified_pattern :=
  fun v => p (valuationXchange_iter v to_rename renaming).

Definition qterm_rename_vars_with
  (p : quantified_term) (to_rename renaming : list Name)
  : quantified_term :=
  fun v => p (valuationXchange_iter v to_rename renaming).

Lemma qterm_rename_vars_with_valuation p to_rename renaming v :
  qterm_rename_vars_with p to_rename renaming v
    =
  p (valuationXchange_iter v to_rename renaming).
Proof. done. Qed.

Lemma arl_vars_eq_rename_iter vars1 vars2_list v1 v2 :
  length vars2_list = size vars1 ->
  NoDup vars2_list ->
  vars1 ## list_to_set vars2_list ->
  ARLVarsEq NameSet (list_to_set vars2_list) v1 v2 ->
  ARLVarsEq NameSet vars1
    (valuationXchange_iter v1 (elements vars1) vars2_list)
    (valuationXchange_iter v2 (elements vars1) vars2_list).
Proof.
  intros Hlen Hnodup2 Hdisj Heqvars.
  constructor; intros x Hx.
  apply elem_of_elements in Hx as Hex.
  apply elem_of_list_lookup in Hex as [n Hnx].
  apply lookup_lt_Some in Hnx as Hn.
  unfold size, set_size in Hlen; cbn in Hlen.
  rewrite <- Hlen in Hn.
  apply lookup_lt_is_Some in Hn as [y Hny].
  rewrite !valuationXchange_iter_left with (n := n) (y := y).
  - by apply Heqvars, elem_of_list_to_set, elem_of_list_lookup; eexists.
  - by apply NoDup_elements.
  - done.
  - by intros; eapply Hdisj; [apply elem_of_elements | apply elem_of_list_to_set].
  - done.
  - done.
  - by apply NoDup_elements.
  - done.
  - by intros; eapply Hdisj; [apply elem_of_elements | apply elem_of_list_to_set].
  - done.
  - done.
Qed.

Lemma pattern_dependent_vars_rename_pattern p vars1 vars2_list :
  pattern_dependent_vars NameSet p vars1 ->
  length vars2_list = size vars1 ->
  NoDup vars2_list ->
  vars1 ## list_to_set vars2_list ->
  pattern_dependent_vars NameSet (qpattern_rename_vars_with p (elements vars1) vars2_list) (list_to_set vars2_list).
Proof.
  intros Hfve Hlen Hnodup2 Hdisj v1 v2 Heqvars.
  by apply Hfve, arl_vars_eq_rename_iter.
Qed.

Lemma pattern_dependent_vars_rename_term (p : quantified_term) vars1 vars2_list :
  pattern_dependent_vars NameSet p vars1 ->
  length vars2_list = size vars1 ->
  NoDup vars2_list ->
  vars1 ## list_to_set vars2_list ->
  pattern_dependent_vars NameSet (qterm_rename_vars_with p (elements vars1) vars2_list) (list_to_set vars2_list).
Proof.
  intros Hfve Hlen Hnodup2 Hdisj v1 v2 Heqvars.
  by apply Hfve, arl_vars_eq_rename_iter.
Qed.

Lemma qterm_rename_vars_with_valuation_rev (p : quantified_term) to_rename renaming :
  pattern_dependent_vars NameSet p (list_to_set to_rename) ->
  NoDup to_rename ->
  NoDup renaming ->
  length to_rename = length renaming ->
  (forall x, x ∈ to_rename -> x ∈ renaming -> False) ->
  forall v, p v = qterm_rename_vars_with p to_rename renaming (valuationXchange_iter v to_rename renaming).
Proof.
  intros Henough Hnodup1 Hnodup2 Hlength Hdisj v; unfold qterm_rename_vars_with.
  apply (Henough v (valuationXchange_iter (valuationXchange_iter v to_rename renaming)
    to_rename renaming)); [| done].
  constructor; intros x Hx.
  by rewrite valuationXchange_iter_twice.
Qed.

Lemma qpattern_rename_vars_with_valuation_rev p to_rename renaming :
  pattern_dependent_vars NameSet p (list_to_set to_rename) ->
  NoDup to_rename ->
  NoDup renaming ->
  length to_rename = length renaming ->
  (forall x, x ∈ to_rename -> x ∈ renaming -> False) ->
  forall v, p v ≡ qpattern_rename_vars_with p to_rename renaming (valuationXchange_iter v to_rename renaming).
Proof.
  intros Henough Hnodup1 Hnodup2 Hlength Hdisj v; unfold qterm_rename_vars_with.
  apply (Henough v (valuationXchange_iter (valuationXchange_iter v to_rename renaming)
    to_rename renaming)).
  constructor; intros x Hx.
  by rewrite valuationXchange_iter_twice.
Qed.

Context `{Infinite Name}.

Program Definition rewrite_rule_refresh_vars (r : RewriteRule NameSet) (avoid : NameSet) : RewriteRule NameSet :=
  let vars_list := elements (vars r) in
  let fresh_vars := fresh_list (length vars_list) (avoid ∪ vars r) in
  let vars_lhs_positions := find_positions vars_list (elements (vars_lhs r)) in
  let fresh_vars_lhs := multiple_lookups fresh_vars vars_lhs_positions in
  {|
    vars := list_to_set fresh_vars;
    vars_lhs := list_to_set fresh_vars_lhs;
    lhs := qterm_rename_vars_with (lhs r) vars_list fresh_vars;
    requires := qpattern_rename_vars_with (requires r) vars_list fresh_vars;
    rhs := qterm_rename_vars_with (rhs r) vars_list fresh_vars;
    ensures := qpattern_rename_vars_with (ensures r) vars_list fresh_vars;
  |}.
Next Obligation.
  intros * x.
  rewrite !elem_of_list_to_set; intro Hx.
  apply elem_of_list_omap in Hx as (? & ? & ?).
  by apply elem_of_list_lookup; eexists.
Qed.
Next Obligation.
  intros * v1 v2 Heqvars.
  apply lhs_vars.
  specialize (arl_vars_eq_rename_iter (vars_lhs r) fresh_vars_lhs v1 v2).
Next Obligation.
  intros [] * ?; apply ensures_predicate.
Qed.
Next Obligation.
  intros.
  eapply pattern_dependent_vars_rename_term.
  - by apply lhs_vars.
  - by apply fresh_list_length.
  - apply NoDup_fresh_list.
  - intros x Hx1 Hx2.
    eapply Forall_fresh_elem_of.
    + apply Forall_fresh_list.
    + by apply elem_of_list_to_set in Hx2.
    + by apply elem_of_union; right.
Qed.
Next Obligation.
  intros.
  eapply pattern_dependent_vars_rename_term.
  - by apply rhs_vars.
  - by apply fresh_list_length.
  - apply NoDup_fresh_list.
  - intros x Hx1 Hx2.
    eapply Forall_fresh_elem_of.
    + apply Forall_fresh_list.
    + by apply elem_of_list_to_set in Hx2.
    + by apply elem_of_union; right.
Qed.
Next Obligation.
  intros.
  eapply pattern_dependent_vars_rename_pattern.
  - by apply requires_vars.
  - by apply fresh_list_length.
  - apply NoDup_fresh_list.
  - intros x Hx1 Hx2.
    eapply Forall_fresh_elem_of.
    + apply Forall_fresh_list.
    + by apply elem_of_list_to_set in Hx2.
    + by apply elem_of_union; right.
Qed.
Next Obligation.
  intros.
  eapply pattern_dependent_vars_rename_pattern.
  - by apply ensures_vars.
  - by apply fresh_list_length.
  - apply NoDup_fresh_list.
  - intros x Hx1 Hx2.
    eapply Forall_fresh_elem_of.
    + apply Forall_fresh_list.
    + by apply elem_of_list_to_set in Hx2.
    + by apply elem_of_union; right.
Qed.

Lemma rewrite_rule_refresh_vars_disj r avoid :
  vars (rewrite_rule_refresh_vars r avoid) ## (avoid ∪ vars r).
Proof.
  cbn; intros x Hx1 Hx2.
  eapply Forall_fresh_elem_of.
  + apply Forall_fresh_list.
  + by apply elem_of_list_to_set in Hx1.
  + done.
Qed.

Lemma rewrite_rule_refresh_vars_disj_original r avoid :
  vars (rewrite_rule_refresh_vars r avoid) ## vars r.
Proof.
  cbn; intros x Hx1 Hx2.
  eapply rewrite_rule_refresh_vars_disj; [by exact Hx1 |].
  by apply elem_of_union; right.
Qed.

Lemma rewrite_rule_refresh_vars_disj_avoid r avoid :
  vars (rewrite_rule_refresh_vars r avoid) ## avoid.
Proof.
  cbn; intros x Hx1 Hx2.
  eapply rewrite_rule_refresh_vars_disj; [by exact Hx1 |].
  by apply elem_of_union; left.
Qed.

#[local] Lemma TransitionFromRuleInstance_refresh_vars r avoid
  (refreshed := rewrite_rule_refresh_vars r avoid)
  (vars_list := elements (vars r))
  (fresh_vars := fresh_list (length vars_list) (avoid ∪ vars r))
  (v : Valuation Name)
  (a b : idomain) :
  TransitionFromRuleInstance r v a b
    ->
  TransitionFromRuleInstance
    (rewrite_rule_refresh_vars r avoid)
    (valuationXchange_iter v vars_list fresh_vars)
    a b.
Proof.
  intros []; constructor; cbn.
  - unfold qterm_rename_vars_with.
    rewrite valuationXchange_iter_twice.
    + done.
    + apply NoDup_elements.
    + apply NoDup_fresh_list.
    + intros x Hx1 Hx2.
      eapply Forall_fresh_elem_of.
      * apply Forall_fresh_list.
      * done.
      * by apply elem_of_union; right; apply elem_of_elements.
    + by rewrite fresh_list_length.
  - unfold qterm_rename_vars_with.
    rewrite valuationXchange_iter_twice.
    + done.
    + apply NoDup_elements.
    + apply NoDup_fresh_list.
    + intros x Hx1 Hx2.
      eapply Forall_fresh_elem_of.
      * apply Forall_fresh_list.
      * done.
      * by apply elem_of_union; right; apply elem_of_elements.
    + by rewrite fresh_list_length.
  - unfold qpattern_rename_vars_with.
    rewrite valuationXchange_iter_twice.
    + done.
    + apply NoDup_elements.
    + apply NoDup_fresh_list.
    + intros x Hx1 Hx2.
      eapply Forall_fresh_elem_of.
      * apply Forall_fresh_list.
      * done.
      * by apply elem_of_union; right; apply elem_of_elements.
    + by rewrite fresh_list_length.
  - unfold qpattern_rename_vars_with.
    rewrite valuationXchange_iter_twice.
    + done.
    + apply NoDup_elements.
    + apply NoDup_fresh_list.
    + intros x Hx1 Hx2.
      eapply Forall_fresh_elem_of.
      * apply Forall_fresh_list.
      * done.
      * by apply elem_of_union; right; apply elem_of_elements.
    + by rewrite fresh_list_length.
Qed.

#[local] Lemma TransitionFromRuleInstance_refresh_vars_rev r avoid
  (refreshed := rewrite_rule_refresh_vars r avoid)
  (vars_list := elements (vars r))
  (fresh_vars := fresh_list (length vars_list) (avoid ∪ vars r))
  (v : Valuation Name)
  (a b : idomain) :
  TransitionFromRuleInstance
    (rewrite_rule_refresh_vars r avoid) v a b
    ->
  TransitionFromRuleInstance
    r (valuationXchange_iter v vars_list fresh_vars) a b.
Proof. by intros []; constructor; cbn; done. Qed.

Lemma TransitionFromRule_refresh_vars r avoid :
  forall a b, TransitionFromRule r a b <->
    TransitionFromRule (rewrite_rule_refresh_vars r avoid) a b.
Proof.
  intros; split; intros []; econstructor.
  - by apply TransitionFromRuleInstance_refresh_vars.
  - by apply TransitionFromRuleInstance_refresh_vars_rev.
Qed.

End sec_refresh_rule.
