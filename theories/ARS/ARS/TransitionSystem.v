From stdpp Require Import prelude.
From Coq Require Import Classical.
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

Definition complete_transition_chain : trace idomain -> Prop :=
  ForAllSuffixes
    (fun tr => match tr with
    | Tnil a => irreducible a
    | Tcons a tr => transition a (hd tr)
    end).

Lemma complete_transition_chain_nil : forall a, irreducible a -> complete_transition_chain (Tnil a).
Proof. by intros; apply Forall_nil. Qed.

Lemma complete_transition_chain_delay : forall a tr,
  transition a (hd tr) -> complete_transition_chain tr -> complete_transition_chain (Tcons a tr).
Proof. by intros; eapply Forall_delay. Qed.

Lemma complete_transition_chain_nth_tl_keep_nil tr n : complete_transition_chain tr -> complete_transition_chain (nth_tl_keep_nil tr n).
Proof. by apply ForAllSuffixes_drop_n. Qed.

Section sec_traces.

End sec_traces.

End sec_transition_system.
