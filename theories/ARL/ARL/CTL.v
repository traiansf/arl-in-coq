From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARL Require Import Traces TransitionSystem.

Section sec_CTL_defs.

Context `{TransitionSystem}.

(** The set of elements which in one step can transition to <<b>>. *)
Definition EX_fs (b : idomain) : Ensemble idomain := flip transition b.

(** The set of elements which in one step can transition into <<B>>. *)
Definition EX_functor (B : Ensemble idomain) : Ensemble idomain := filtered_union B EX_fs.

(**
  The set of elements whose all one step transitions lead into <<B>>
  Note that this set includes irreducible elements.
*)
Definition AX_functor (B : Ensemble idomain) : Ensemble idomain :=
  complement (EX_functor (complement B)).

(**
  The set of elements for which all complete transition chains starting in them
  pass through an element in <<P>> (in a finite number of transitions).
  Note that this set only includes irreducible elements if they are in <<P>>.
*)
Definition AF_ts (P : Ensemble idomain) (a : idomain) : Prop :=
  forall tr : trace idomain, hd tr = a -> complete_transition_chain tr ->
  Exists1 (fun b : idomain => b ∈ P) tr.

(**
  The set of elements for which there exists a complete transition chains
  starting in them passing through an element in <<P>> (in a finite number
  of transitions).
  Note that this set only includes irreducible elements if they are in <<P>>.
*)
Definition EF_ts_alt (P : Ensemble idomain) (a : idomain) : Prop :=
  exists tr : trace idomain, hd tr = a /\ complete_transition_chain tr /\
  Exists1 (fun b : idomain => b ∈ P) tr.

(** A simpler definition of exists-finally, using finite witnesses. *)
Definition EF_ts (P : Ensemble idomain) (a : idomain) : Prop :=
  exists l : list idomain, transition_sequence (a :: l) /\ List.last l a ∈ P.

Lemma EF_ts_iff P : EF_ts_alt P ≡ EF_ts P.
Proof.
  intro a; split.
  - intros (tr & Heq_a & Htr & Hex).
    apply Exists1_exists in Hex as [n Hnth].
    rewrite <- (trace_prefix_last tr n a) in Hnth.
    destruct tr; subst; [ by exists []; repeat constructor |].
    exists (trace_prefix tr n); split.
    + by apply complete_transition_chain_prefix with (n := S n) in Htr.
    + by erewrite <- last_cons.
  - intros (ts & Hts & Hp).
    destruct (transition_sequence_to_complete_transition_chain a ts Hts)
      as (tr & Htr & Heqts).
    exists tr; split_and!; [by destruct tr; inversion Heqts | done |].
    apply Exists1_exists.
    exists (length ts).
    by rewrite <- trace_prefix_last with (d := a), Heqts, last_cons.
Qed.

End sec_CTL_defs.

Section sec_CTL_properties.

Context `{TransitionSystem}.

Lemma transition_image_EX_preimage A : transition_image_functor A ≡ preimage EX_fs A.
Proof.
  intros a; unfold transition_image_functor.
  rewrite elem_of_preimage, elem_of_filtered_union.
  unfold transition_image, EX_fs; cbn; firstorder.
Qed.

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
  specialize (Hn (nth_tl_keep_nil tr n) eq_refl (complete_transition_chain_nth_tl_keep_nil tr n Htr)).
  apply Exists1_exists in Hn as [m Hm].
  apply Exists1_exists; eexists.
  by erewrite nth_keep_nil_twice.
Qed.

#[export] Instance EF_ts_proper_subseteq :
  Proper ((⊆) ==> (⊆)) EF_ts.
Proof.
  intros A B Hincl a (ts & Hts & Hlst).
  by eexists; split_and!; [..| apply Hincl].
Qed.

Lemma EF_ts_idempotent φ :
  EF_ts (EF_ts φ)
    ≡
  EF_ts φ.
Proof.
  apply set_equiv_subseteq; split;
    intros a (tr & Htr & Hlst).
  - destruct Hlst as (tr' & Htr' & Hlst').
    exists (tr ++ tr').
    split; [| by rewrite last_app].
    by apply ForAllConsecutivePairsList_app.
  - eexists; split_and!; [done.. |].
    by exists []; split; [repeat constructor |].
Qed.

End sec_CTL_properties.
