From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARS Require Import Traces TransitionSystem.

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

End sec_CTL_properties.
