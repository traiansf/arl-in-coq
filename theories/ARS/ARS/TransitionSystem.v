From stdpp Require Import prelude.
From Coq Require Import ClassicalEpsilon.
From sets Require Import Ensemble.
From ARS.Lib Require Import Traces.


Class TransitionSystem (idomain : Type) := transition : relation idomain.


Section sec_transition_system.

Context `{TransitionSystem}.

Definition transition_image (a : idomain) : Ensemble idomain := transition a.
Definition transition_image_functor (A : Ensemble idomain) : Ensemble idomain := filtered_union A transition_image.

Definition reducible (a : idomain) : Prop := exists b, transition a b.
Definition irreducible (a : idomain) : Prop := ~ reducible a.

Lemma irreducible_transition_image a : irreducible a <-> transition_image a ≡ ∅.
Proof. by unfold irreducible, reducible; set_solver. Qed.

Lemma irreducible_iff_no_transition a :
  irreducible a <-> forall b, ~ transition a b.
Proof. by firstorder. Qed.

Lemma reducible_transition_image a : reducible a <-> ∅ ⊂ transition_image a.
Proof.
  destruct (classic (reducible a)) as [| Ha];
    [by split; [unfold reducible, transition_image; set_solver |] |].
  apply irreducible_transition_image in Ha as Hempty.
  setoid_rewrite irreducible_iff_no_transition in Ha.
  unfold transition_image in *.
  unfold reducible.
  by set_solver.
Qed.

Lemma transition_image_subseteq a A :
  transition_image a ⊆ A
    <->
  forall b, transition a b -> b ∈ A.
Proof. firstorder. Qed.

Inductive TransitionSequence : list idomain -> Prop :=
| ts_singleton : forall a b, transition a b -> TransitionSequence [a; b]
| ts_more : forall a b l, transition a b -> TransitionSequence (b :: l) ->
    TransitionSequence (a :: b :: l).

Definition transition_sequence : list idomain -> Prop :=
  ForAllConsecutivePairsList transition.

Lemma transition_sequence_iff a b trs :
  TransitionSequence (a :: b :: trs)
    <->
  transition_sequence (a :: b :: trs).
Proof.
  remember (a :: b :: trs) as abtrs.
  revert a b trs Heqabtrs.
  induction abtrs; [by inversion 1 |].
  inversion 1; subst.
  split; inversion 1; subst.
  - do 2 (constructor; [done |]).
    by constructor.
  - constructor; [done |].
    destruct trs; [by constructor; [| constructor] |].
    by eapply IHabtrs.
  - destruct trs; [by constructor 1 |].
    constructor; [done |].
    by eapply IHabtrs.
Qed.

Record CompleteTransitionChain (tr : trace idomain) : Prop :=
{
  ctc_transition_chain : ForAllConsecutivePairs transition tr;
  ctc_complete : forall a, finalT tr a -> irreducible a
}.

Definition complete_transition_chain : trace idomain -> Prop :=
  ForAllSuffixes
    (fun tr => match tr with
    | Tnil a => irreducible a
    | Tcons a tr => transition a (hd tr)
    end).

Lemma complete_transition_chain_iff tr :
  CompleteTransitionChain tr
    <->
  complete_transition_chain tr.
Proof.
  split; [| intro Htr; split].
  - intros [Hchain Hcomplete].
    revert tr Hchain Hcomplete.
    cofix Hind; intros [] ? ?;
      [by constructor; apply Hcomplete; constructor |].
    inversion Hchain; subst.
    constructor; [done |].
    apply Hind; [done |].
    by intros; apply Hcomplete; constructor.
  - revert tr Htr.
    cofix Hind; intros [] ?; [by constructor |].
    inversion Htr; subst.
    constructor; [done |].
    by apply Hind.
  - intros a Ha; revert Htr.
    by induction Ha; inversion 1; subst; [| apply IHHa].
Qed.

Lemma complete_transition_chain_nil : forall a, irreducible a -> complete_transition_chain (Tnil a).
Proof. by intros; apply Forall_nil. Qed.

Lemma complete_transition_chain_delay : forall a tr,
  transition a (hd tr) -> complete_transition_chain tr -> complete_transition_chain (Tcons a tr).
Proof. by intros; eapply Forall_delay. Qed.

Lemma complete_transition_chain_nth_tl_keep_nil tr n : complete_transition_chain tr -> complete_transition_chain (nth_tl_keep_nil tr n).
Proof. by apply ForAllSuffixes_drop_n. Qed.

Lemma complete_transition_chain_prefix tr :
  complete_transition_chain tr ->
  forall n, transition_sequence (trace_prefix tr n).
Proof.
  intros Hchain.
  by apply forall_consecutive_pairs_trace_prefix, ctc_transition_chain,
    complete_transition_chain_iff.
Qed.

Section sec_iterated_choice.

Context
  (A : Ensemble idomain)
  (choose: {a : idomain | ¬ irreducible a} → idomain).

CoFixpoint iterated_choice
  (a : idomain)
  : trace idomain
  :=
  match (excluded_middle_informative (irreducible a)) with
  | left _ => Tnil a
  | right Hnot_irreducible =>
    Tcons a (iterated_choice (choose (exist _ a Hnot_irreducible)))
  end.

Lemma iterated_choice_unfold
  (a : idomain)
  : iterated_choice a
    =
    match (excluded_middle_informative (irreducible a)) with
    | left _ => Tnil a
    | right Hnot_irreducible =>
      Tcons a (iterated_choice (choose (exist _ a Hnot_irreducible)))
    end.
Proof. by apply trace_eq_hd_tl; done. Qed.

Lemma iterated_choice_hd (a : idomain) :
  hd (iterated_choice a) = a.
Proof.
  rewrite iterated_choice_unfold.
  by destruct (excluded_middle_informative (irreducible a)).
Qed.

End sec_iterated_choice.

Lemma complete_transition_chain_from_head :
  forall a, exists tr : trace idomain, hd tr = a /\ complete_transition_chain tr.
Proof.
  assert (Hall_ex :
   forall x : {a : idomain | ~ irreducible a},
                    exists a' : idomain, transition (` x) a').
  {
    intros (a0 & Hnot_irreducible0).
    by apply NNPP.
  }
  apply choice in Hall_ex as [choose Hchoose].
  intro a.
  exists (iterated_choice choose a).
  split; [by apply iterated_choice_hd |].
  revert a; cofix Hind; intro a.
  rewrite iterated_choice_unfold.
  destruct (excluded_middle_informative (irreducible a));
    [by apply Forall_nil |].
  apply Forall_delay; [| by apply Hind].
  rewrite iterated_choice_hd.
  by apply (Hchoose (exist _ a n)).
Qed.

Lemma transition_sequence_to_complete_transition_chain :
  forall a ts, transition_sequence (a :: ts) ->
  exists tr, complete_transition_chain tr /\
    trace_prefix tr (S (length ts)) = a :: ts.
Proof.
  intros a ts Hts.
  pose (lst := List.last ts a).
  destruct (complete_transition_chain_from_head lst) as (tr & Heqlst & Htr).
  exists (trace_prepend (removelast (a :: ts)) tr).
  split.
  - apply complete_transition_chain_iff; split.
    + apply forall_consecutive_pairs_trace_prepend;
        [by apply complete_transition_chain_iff | done |].
      by rewrite last_cons.
    + intros final; rewrite <- trace_prepend_finalT.
      by apply complete_transition_chain_iff.
  - remember (a :: ts) as ats; clear Hts; revert a ts lst Heqlst Heqats.
    induction ats; [by inversion 1 |]; intros.
    inversion Heqats; subst; clear Heqats.
    destruct ts; subst lst; [by cbn in Heqlst; subst a0; destruct tr |].
    rewrite last_cons in Heqlst.
    specialize (IHats _ _ Heqlst eq_refl).
    by rewrite <- IHats at 3.
Qed.

Section sec_traces.

End sec_traces.

End sec_transition_system.
