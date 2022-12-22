From stdpp Require Import prelude.
From Coq Require Import ClassicalEpsilon.
From sets Require Import Ensemble.
From ARS.Lib Require Import Traces.


Class TransitionSystem (idomain : Type) := transition : relation idomain.


Section sec_transition_system.

Context `{TransitionSystem}.

Definition EX_fs (b : idomain) : Ensemble idomain := flip transition b.
Definition EX_functor (B : Ensemble idomain) : Ensemble idomain := filtered_union B EX_fs.

Definition transition_image (a : idomain) : Ensemble idomain := transition a.
Definition transition_image_functor (A : Ensemble idomain) : Ensemble idomain := filtered_union A transition_image.

Lemma transition_image_EX_preimage A : transition_image_functor A ≡ preimage EX_fs A.
Proof.
  intros a; unfold transition_image_functor.
  rewrite elem_of_preimage, elem_of_filtered_union.
  unfold transition_image, EX_fs; cbn; firstorder.
Qed.

Definition AX_functor (B : Ensemble idomain) : Ensemble idomain :=
  complement (EX_functor (complement B)).

Definition reducible (a : idomain) : Prop := exists b, transition a b.
Definition stuck (a : idomain) : Prop := ~ reducible a.

Lemma stuck_transition_image a : stuck a <-> transition_image a ≡ ∅.
Proof. by unfold stuck, reducible; set_solver. Qed.

Lemma stuck_iff_no_transition a :
  stuck a <-> forall b, ~ transition a b.
Proof. by firstorder. Qed.

Lemma reducible_transition_image a : reducible a <-> ∅ ⊂ transition_image a.
Proof.
  destruct (classic (reducible a)) as [| Ha];
    [by split; [unfold reducible, transition_image; set_solver |] |].
  apply stuck_transition_image in Ha as Hempty.
  setoid_rewrite stuck_iff_no_transition in Ha.
  unfold transition_image in *.
  unfold reducible.
  by set_solver.
Qed.

Lemma transition_image_subseteq a A :
  transition_image a ⊆ A
    <->
  forall b, transition a b -> b ∈ A.
Proof. firstorder. Qed.

Section sec_traces.

Definition validTEX : trace idomain -> Prop :=
  ForAllSuffixes
    (fun tr => match tr with
    | Tnil a => stuck a
    | Tcons a tr => transition a (hd tr)
    end).

Lemma validTEX_nil : forall a, stuck a -> validTEX (Tnil a).
Proof. by intros; apply Forall_nil. Qed.

Lemma validTEX_delay : forall a tr,
  transition a (hd tr) -> validTEX tr -> validTEX (Tcons a tr).
Proof. by intros; eapply Forall_delay. Qed.

Lemma validTEX_nth_tl_keep_nil tr n : validTEX tr -> validTEX (nth_tl_keep_nil tr n).
Proof. by apply ForAllSuffixes_drop_n. Qed.

Definition AF_ts (P : Ensemble idomain) (a : idomain) : Prop :=
  forall tr : trace idomain, hd tr = a -> validTEX tr ->
  Exists1 (fun b : idomain => b ∈ P) tr.

#[export] Instance AF_ts_proper_subseteq :
  Proper ((⊆) ==> (⊆)) AF_ts.
Proof.
  intros A B Hincl a Ha tr Heq_a Htr.
  by eapply Exists1_weaken; [| apply Ha].
Qed.

Lemma AF_ts_idempotent φ :
  AF_ts (AF_ts φ)
    ≡
  AF_ts φ.
Proof.
  apply set_equiv_subseteq; split;
    [| by intros a Ha tr <- _;  constructor 1].
  intros a Ha tr Heq_a Htr.
  specialize (Ha tr Heq_a Htr).
  apply Exists1_exists in Ha as [n Hn].
  specialize (Hn (nth_tl_keep_nil tr n) eq_refl (validTEX_nth_tl_keep_nil tr n Htr)).
  apply Exists1_exists in Hn as [m Hm].
  apply Exists1_exists; eexists.
  by erewrite nth_keep_nil_twice.
Qed.

End sec_traces.

Section sec_transition_system_deduction_rules.

Lemma rule_of_consequence φ φ' ψ ψ' :
  φ ⊆ φ' -> φ' ⊆ AF_ts ψ' -> ψ' ⊆ ψ ->
  φ ⊆ AF_ts ψ.
Proof.
  intros Hφ HAF Hψ.
  do 2 (etransitivity; [done |]).
  by rewrite Hψ.
Qed.

Lemma rule_of_reflexivity φ : φ ⊆ AF_ts φ.
Proof.
  intros a Ha tr <- _.
  by constructor 1.
Qed.

Lemma rule_of_transitivity φ χ ψ :
  φ ⊆ AF_ts χ ->
  χ ⊆ AF_ts ψ ->
  φ ⊆ AF_ts ψ.
Proof.
  intros Hφ Hχ.
  etransitivity; [done |].
  rewrite Hχ.
  by rewrite AF_ts_idempotent.
Qed.

Lemma rule_of_disjunction φ1 φ2 ψ :
  φ1 ⊆ AF_ts ψ ->
  φ2 ⊆ AF_ts ψ ->
  φ1 ∪ φ2 ⊆ AF_ts ψ.
Proof. by set_solver. Qed.

Lemma rule_of_generalization `(φ : qspace -> Ensemble idomain) ψ :
  (forall i, φ i ⊆ AF_ts ψ) ->
  indexed_union φ ⊆ AF_ts ψ.
Proof.
  intros Hall a; rewrite elem_of_indexed_union.
  intros [i Hai].
  by eapply Hall.
Qed.

Lemma rule_of_simple_step φ : φ ⊆ reducible ->
  φ ⊆ AF_ts (transition_image_functor φ).
Proof.
  intros Hred a Ha tr <- Htr.
  inversion Htr as [a Hstuck| a tr' Ht _]; subst;
    [by unfold stuck in Hstuck; contradict Hstuck; apply Hred |].
  apply Exists1_exists; exists 1.
  rewrite nth_keep_nil_cons.
  apply elem_of_filtered_union.
  eexists; split; [done |].
  by rewrite nth_keep_nil_0.
Qed.

Section sec_rule_of_induction.

Definition restrictR (R : relation idomain) (X : Ensemble idomain) : relation idomain :=
  fun a b => a ∈ X /\ b ∈ X /\ R a b.

Context
  `{qspace : Type} (* instances of quantifiers *)
  (measure : qspace -> idomain)
  (prec : relation idomain)
  (Hwf : well_founded prec)
  {index}
  (φ : index -> qspace -> Ensemble idomain)
  (ψ : index -> qspace -> Ensemble idomain)
  (Hind : forall q0,
    (forall q, prec (measure q) (measure q0) ->
      forall i, φ i q ⊆ AF_ts (ψ i q)) ->
    forall i, φ i q0 ⊆ AF_ts (ψ i q0))
  .

Lemma rule_of_induction :
    forall i q, φ i q ⊆ AF_ts (ψ i q).
Proof.
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

End sec_rule_of_induction.

End sec_transition_system_deduction_rules.

Section sec_fix_points.

Context
  (ψ : Ensemble idomain)
  .

Definition AF_ts_fixed_point_functor (X : Ensemble idomain) : Ensemble idomain :=
  fun a => a ∈ ψ \/ reducible a /\ forall b, transition a b -> b ∈ X.

Lemma AF_ts_pre_fixpoint :
  pre_fixpoint AF_ts_fixed_point_functor (AF_ts ψ).
Proof.
  intro a.
  intros [Ha | [Hnot_stuck Hall]] tr Hhd Htr;
    [by subst; apply Exists_now |].
  inversion Htr as [? Hstuck | ? ? Hfirst Hrest]; subst; [done |].
  by eapply Exists_delay, Hall.
Qed.

Lemma AF_ts_post_fixpoint :
  post_fixpoint AF_ts_fixed_point_functor (AF_ts ψ).
Proof.
  intros a Hall.
  unfold AF_ts_fixed_point_functor, elem_of, pow_set_elem_of.
  classical_right.
  split.
  - destruct (classic (reducible a)); [done |].
    specialize (Hall (Tnil a)).
    by feed specialize Hall; [| eapply validTEX_nil | inversion Hall].
  - intros b Hb tr <- Htr.
    specialize (Hall (Tcons a tr)).
    by feed specialize Hall; [| eapply validTEX_delay | inversion Hall].
Qed.

Lemma AF_ts_fixpoint :
  fixpoint AF_ts_fixed_point_functor (AF_ts ψ).
Proof.
  split.
  - apply (AF_ts_pre_fixpoint x).
  - apply (AF_ts_post_fixpoint x).
Qed.

Lemma not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint
  A (Hpre: pre_fixpoint AF_ts_fixed_point_functor A) :
  forall a, a ∉ A -> a ∉ ψ.
Proof.
  intros a Hna; contradict Hna; apply Hpre.
  by left.
Qed.

Lemma not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint_not_stuck
  A (Hpre: pre_fixpoint AF_ts_fixed_point_functor A)
  (a: idomain)
  (Hna: a ∉ A)
  (Hnot_stuck : ~ stuck a)
  : exists a', a' ∉ A /\ transition a a'.
Proof.
  specialize (Hpre a).
   apply imply_to_or in Hpre as [Hpre |]; [| done].
  apply not_or_and in Hpre as [_ Hpre].
  apply not_and_or in Hpre as [| Hpre]; [done |].
  apply not_all_ex_not in Hpre as [a' Ha'].
  apply imply_to_and in Ha' as [].
  by exists a'.
Qed.

Section sec_iterated_choice.

Context
  (A : Ensemble idomain)
  (choose: {a : idomain | (a ∉ A) ∧ ¬ stuck a} → idomain)
  (Hchoose_not_in: forall x : {a : idomain | (a ∉ A) ∧ ¬ stuck a}, choose x ∉ A).

CoFixpoint iterated_choice
  (a : idomain)
  (Ha : a ∉ A)
  : trace idomain
  :=
  match (excluded_middle_informative (stuck a)) with
  | left _ => Tnil a
  | right Hnot_stuck =>
    Tcons a (iterated_choice _ (Hchoose_not_in (exist _ a (conj Ha Hnot_stuck))))
  end.

Lemma iterated_choice_unfold
  (a : idomain)
  (Ha : a ∉ A)
  : iterated_choice a Ha
    =
    match (excluded_middle_informative (stuck a)) with
    | left _ => Tnil a
    | right Hnot_stuck =>
      Tcons a (iterated_choice _ (Hchoose_not_in (exist _ a (conj Ha Hnot_stuck))))
    end.
Proof. by apply trace_eq_hd_tl; done. Qed.

Lemma iterated_choice_hd (a : idomain) (Ha : a ∉ A) :
  hd (iterated_choice a Ha) = a.
Proof.
  rewrite iterated_choice_unfold.
  by destruct (excluded_middle_informative (stuck a)).
Qed.

End sec_iterated_choice.

Lemma AF_ts_least_pre_fixpoint A :
  pre_fixpoint AF_ts_fixed_point_functor A ->
  AF_ts ψ ⊆ A.
Proof.
  intros Hpre.
  unfold AF_ts.
  intro a; unfold elem_of at 1, pow_set_elem_of at 1; cbn.
  intros Hall.
  destruct (classic (a ∈ A)) as [| Hna]; [done |]; exfalso.
  cut (exists tr, hd tr = a /\ validTEX tr /\
      ForAll1 (fun b => b ∉ A) tr).
  {
    intros (tr & Hhd & Htr & Hall_b).
    specialize (Hall tr Hhd Htr).
    apply Exists1_exists in Hall as (n & Hn).
    contradict Hn.
    by eapply not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint, ForAll1_forall.
  }
  clear Hall.
  assert (Hall_ex :
   forall x : {a : idomain | a ∉ A /\ ~ stuck a},
                    exists a' : idomain, (a' ∉ A) /\ transition (` x) a').
  {
    intros (a0 & Hna0 & Hnot_stuck0).
    by apply not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint_not_stuck.
  }
  apply choice in Hall_ex as [choose Hchoose].
  assert (Hchoose_not_in : forall x : {a : idomain | (a ∉ A) ∧ ¬ stuck a},
    choose x ∉ A) by firstorder.
  exists (iterated_choice _ choose Hchoose_not_in _ Hna).
  repeat split.
  - by apply iterated_choice_hd.
  - unfold validTEX.
    revert a Hna.
    cofix CIH; intros a Hna.
    rewrite iterated_choice_unfold.
    destruct (excluded_middle_informative (stuck a)) as [| Hnstuck];
      [by apply Forall_nil |].
    apply Forall_delay.
    + rewrite iterated_choice_hd.
      change a with (` (exist (fun a => (a ∉ A) ∧ ¬ stuck a) a (conj Hna Hnstuck))).
      by apply Hchoose.
    + apply CIH.
  - revert a Hna.
    cofix CIH; intros a Hna.
    rewrite iterated_choice_unfold.
    destruct (excluded_middle_informative (stuck a));
      [by apply Forall_nil |].
    apply Forall_delay; [done |].
    by apply CIH.
Qed.

End sec_fix_points.

End sec_transition_system.
