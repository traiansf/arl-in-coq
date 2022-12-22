From stdpp Require Import prelude.
From Coq Require Import Program.Equality.

(**
  Based on

  - https://github.com/runtimeverification/vlsm/blob/master/theories/VLSM/Lib/Traces.v
  - https://github.com/runtimeverification/vlsm/blob/master/theories/VLSM/Lib/TraceProperties.v
*)

CoInductive trace (A : Type) : Type :=
| Tnil : A -> trace A
| Tcons : A -> trace A -> trace A.

Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

Arguments Tnil  {_} _ : assert.
Arguments Tcons {_} _ _ : assert.

Section sec_traces.

Context {A : Type}.

#[local] Notation trace := (trace A).

Definition hd (tr : trace) :=
  match tr with
  | Tnil a => a
  | Tcons a _ => a
  end.

Definition tl_keep_nil (tr : trace) : trace :=
  match tr with
  | Tnil _ => tr
  | Tcons _ tr0 => tr0
  end.

Definition tl_option (tr : trace) : option trace :=
  match tr with
  | Tnil _ => None
  | Tcons _ tr0 => Some tr0
  end.

Lemma trace_eq_hd_tl (s s' : trace) :
  hd s = hd s' -> tl_option s = tl_option s' -> s = s'.
Proof. by destruct s, s'; cbn; intros -> [=]; subst. Qed.

Fixpoint nth_tl_keep_nil (tr : trace) (n : nat) : trace :=
  match n with
  | 0 => tr
  | S n => nth_tl_keep_nil (tl_keep_nil tr) n
  end.

Lemma nth_tl_keep_nil_nil (a : A) : forall m, nth_tl_keep_nil (Tnil a) m = Tnil a.
Proof. by induction m. Qed.

Lemma nth_tl_keep_nil_twice tr n1 n2 :
  nth_tl_keep_nil tr (n1 + n2) = nth_tl_keep_nil (nth_tl_keep_nil tr n1) n2.
Proof.
  revert tr n2.
  induction n1; [done |].
  intros [] *; [by rewrite !nth_tl_keep_nil_nil |].
  by apply IHn1.
Qed.

Definition nth_keep_nil (tr : trace) (n : nat) : A := hd (nth_tl_keep_nil tr n).

Lemma nth_keep_nil_nil (a : A) : forall m, nth_keep_nil (Tnil a) m = a.
Proof. by intros; unfold nth_keep_nil; rewrite nth_tl_keep_nil_nil. Qed.

Lemma nth_keep_nil_0 tr : nth_keep_nil tr 0 = hd tr.
Proof. by destruct tr. Qed.

Lemma nth_keep_nil_cons (a : A) (tr : trace) (n : nat) :
  nth_keep_nil (Tcons a tr) (S n) = nth_keep_nil tr n.
Proof. done. Qed.

Lemma nth_keep_nil_twice tr n1 n2 :
  nth_keep_nil tr (n1 + n2) = nth_keep_nil (nth_tl_keep_nil tr n1) n2.
Proof. by unfold nth_keep_nil; rewrite nth_tl_keep_nil_twice. Qed.

Definition trace_decompose (tr: trace): trace :=
match tr with
| Tnil a => Tnil a
| Tcons a tr' => Tcons a tr'
end.

Lemma trace_destr: forall tr, tr = trace_decompose tr.
Proof. by destruct tr. Qed.

(** ** Bisimulations between traces *)

CoInductive bisim : trace -> trace -> Prop :=
| bisim_nil : forall a,
   bisim (Tnil a) (Tnil a)
| bisim_cons : forall a tr tr',
   bisim tr tr' ->
   bisim (Tcons a tr) (Tcons a tr').

#[export] Instance bisim_refl : Reflexive bisim.
Proof.
  cofix CIH.
  by intros []; [apply bisim_nil | apply bisim_cons, CIH].
Qed.

#[export] Instance bisim_sym : Symmetric bisim.
Proof.
  cofix CIH.
  by intros [] y; inversion 1; subst; [apply bisim_nil | apply bisim_cons, CIH].
Qed.

#[export] Instance bisim_trans : Transitive bisim.
Proof.
  cofix CIH.
  by intros [] y z; inversion 1; subst; inversion 1; subst;
    [apply bisim_nil | eapply bisim_cons, CIH].
Qed.

#[export] Instance bisim_equiv : Equiv trace := bisim.

Lemma bisim_hd: forall tr0 tr1, bisim tr0 tr1 -> hd tr0 = hd tr1.
Proof. by inversion 1; subst. Qed.

(** ** Appending traces to one another *)

CoFixpoint trace_append (tr tr': trace): trace :=
match tr with
| Tnil a => Tcons a tr'
| Tcons a tr0 => Tcons a (trace_append tr0 tr')
end.

#[local] Infix "+++" := trace_append (at level 60, right associativity).

Lemma trace_append_nil : forall a tr, (Tnil a) +++ tr = Tcons a tr.
Proof.
  intros a tr.
  rewrite (trace_destr (Tnil a +++ tr)).
  by destruct tr.
Qed.

Lemma trace_append_cons : forall a tr tr',
  (Tcons a tr) +++ tr' = Tcons a (tr +++ tr').
Proof.
  intros a tr tr'.
  rewrite (trace_destr (Tcons a tr +++ tr')).
  by destruct tr.
Qed.

#[export] Instance trace_append_proper :
  Proper ((≡) ==> (≡) ==> (≡)) trace_append.
Proof.
  cofix CIH.
  intros tr1 tr2 [] tr3 tr4 Htr34.
  - by rewrite 2!trace_append_nil; apply bisim_cons.
  - by rewrite 2!trace_append_cons; apply bisim_cons, CIH.
Qed.

CoInductive ForAllSuffixes (P : trace -> Prop) : trace -> Prop :=
| Forall_nil : forall a, P (Tnil a) -> ForAllSuffixes P (Tnil a)
| Forall_delay : forall a tr, P (Tcons a tr) ->
    ForAllSuffixes P tr ->
    ForAllSuffixes P (Tcons a tr).

Lemma ForallSuffixes_proper_impl (P : trace -> Prop ) `(!Proper ((≡) ==> impl) P) :
  Proper ((≡) ==> impl) (ForAllSuffixes P).
Proof.
  cofix CIH.
  intros tr1 tr2 Heqv Htr1.
  inversion Htr1; subst; inversion Heqv; subst; clear Htr1 Heqv.
  - by apply Forall_nil.
  - apply Forall_delay.
    + eapply Proper0; [| done].
      by apply bisim_cons.
    + by eapply CIH.
Qed.

Lemma ForallSuffixes_proper_iff (P : trace -> Prop ) `(!Proper ((≡) ==> iff) P) :
  Proper ((≡) ==> iff) (ForAllSuffixes P).
Proof.
  cut (Proper (equiv ==> impl) P);
    [by intros ? tr1 tr2 Heqv; split; apply ForallSuffixes_proper_impl |].
  by intros tr1 tr2 ->.
Qed.

Lemma ForAllSuffixes_drop_n (P : trace -> Prop) :
  forall m x, ForAllSuffixes P x -> ForAllSuffixes P (nth_tl_keep_nil x m).
Proof.
  induction m; [done |].
  intros x [].
  - by rewrite nth_tl_keep_nil_nil; constructor.
  - by cbn; apply IHm.
Qed.

Lemma ForAllSuffixes_hd (P : trace -> Prop) (tr : trace) :
  ForAllSuffixes P tr -> P tr.
Proof. by inversion 1. Qed.

Lemma ForAllSuffixes_nth (P : trace -> Prop) :
  forall m x, ForAllSuffixes P x -> P (nth_tl_keep_nil x m).
Proof. by intros; apply ForAllSuffixes_hd, ForAllSuffixes_drop_n. Qed.

Section Co_Induction_ForAllSuffixes.

Context (P : trace -> Prop).

Variable Inv : trace -> Prop.
Hypothesis Inv_subsumption : forall tr : trace, Inv tr -> P tr.
Hypothesis Inv_delay : forall (a : A) (tr : trace), Inv (Tcons a tr) -> Inv tr.

Theorem ForAll_coind : forall tr : trace, Inv tr -> ForAllSuffixes P tr.
Proof.
  cofix CIH; intros [].
  - by intro; apply Forall_nil, Inv_subsumption.
  - intro Hprev.
    apply Forall_delay; [by apply Inv_subsumption |].
    by eapply CIH, Inv_delay.
Qed.

End Co_Induction_ForAllSuffixes.

Lemma ForAllSuffixes_forall (P : trace -> Prop) tr :
  ForAllSuffixes P tr <-> forall n, P (nth_tl_keep_nil tr n).
Proof.
  split.
  - by intros; apply ForAllSuffixes_nth.
  - revert tr; apply ForAll_coind; cbn.
    + by intros tr Htr; apply (Htr 0).
    + by intros a tr Htr n; apply (Htr (S n)).
Qed.

Lemma ForAllSuffixes_and (P Q : trace -> Prop) tr :
  ForAllSuffixes (fun t => P t /\ Q t) tr
    <->
  ForAllSuffixes P tr /\ ForAllSuffixes Q tr.
Proof.
  rewrite !ForAllSuffixes_forall.
  by firstorder.
Qed.

Definition ForAll1 (P : A -> Prop) : trace -> Prop := ForAllSuffixes (P ∘ hd).

Lemma ForAll1_forall (P : A -> Prop) tr :
  ForAll1 P tr <-> forall n, P (nth_keep_nil tr n).
Proof. by apply ForAllSuffixes_forall. Qed.

Inductive ExistsSuffix (P : trace -> Prop) : trace -> Prop :=
| Exists_now : forall tr, P tr -> ExistsSuffix P tr
| Exists_delay : forall a tr,
    ExistsSuffix P tr ->
    ExistsSuffix P (Tcons a tr).

Definition Exists1 (P : A -> Prop) : trace -> Prop := ExistsSuffix (P ∘ hd).

Lemma ExistsSuffix_exists (P : trace -> Prop) tr :
  ExistsSuffix P tr <-> exists n, P (nth_tl_keep_nil tr n).
Proof.
  split.
  - induction 1.
    + by exists 0.
    + destruct IHExistsSuffix as [n Hp].
      by exists (S n).
  - intros [n Hp]. revert tr Hp. induction n; intros; [by constructor |].
    destruct tr.
    + rewrite nth_tl_keep_nil_nil in Hp.
      by apply Exists_now.
    + by apply Exists_delay, IHn.
Qed.

Lemma Exists1_exists (P : A -> Prop) tr :
  Exists1 P tr <-> exists n, P (nth_keep_nil tr n).
Proof. by apply ExistsSuffix_exists. Qed.

Lemma Exists1_weaken (P Q : A -> Prop) tr :
  (forall a, P a -> Q a) ->
  Exists1 P tr -> Exists1 Q tr.
Proof.
  intro Hincl.
  rewrite !Exists1_exists.
  intros [n Hn].
  by exists n; apply Hincl.
Qed.

End sec_traces.

Infix "+++" := trace_append (at level 60, right associativity).

Section sec_trace_properties.

Context {A : Type}.

#[local] Notation trace := (trace A).

(** ** Infiniteness property *)

Definition infiniteT : trace -> Prop :=
  ForAllSuffixes
    (fun tr => match tr with
    | Tnil _ => False
    | _ => True
    end).

#[export] Instance infiniteT_proper_iff : Proper ((≡) ==> iff) infiniteT.
Proof.
  apply ForallSuffixes_proper_iff.
  by intros []; inversion 1.
Qed.

Lemma infiniteT_cons : forall a tr,
  infiniteT (Tcons a tr) <-> infiniteT tr.
Proof. by split; [inversion 1 | apply Forall_delay]. Qed.

(** ** Finiteness property *)

Inductive finiteT : trace -> Prop :=
| finiteT_nil : forall a,
   finiteT (Tnil a)
| finiteT_delay : forall (a : A) tr,
   finiteT tr ->
   finiteT (Tcons a tr).

Lemma finiteT_proper_impl : Proper ((≡) ==> impl) finiteT.
Proof.
  intros tr1 tr2 Heqv Htr1; revert tr2 Heqv.
  induction Htr1; inversion 1; subst; [by constructor |].
  by constructor; apply IHHtr1.
Qed.

#[export] Instance finiteT_proper : Proper ((≡) ==> iff) finiteT.
Proof. by intros tr1 tr2 Heqv; split; apply finiteT_proper_impl. Qed.

Lemma invert_finiteT_delay (a : A) (tr : trace)
  (h : finiteT (Tcons a tr)) : finiteT tr.
Proof. by inversion h. Defined.

Lemma finiteT_bisim_eq : forall tr,
  finiteT tr -> forall tr', tr ≡ tr' -> tr = tr'.
Proof. by induction 1; inversion 1; subst; [| erewrite IHfiniteT]. Qed.

(** Basic connections between finiteness and infiniteness. *)

Lemma finiteT_infiniteT_not : forall tr,
  finiteT tr -> infiniteT tr -> False.
Proof. by intro tr; induction 1; inversion 1. Qed.

Lemma not_finiteT_infiniteT : forall tr,
  ~ finiteT tr -> infiniteT tr.
Proof.
  unfold infiniteT.
  cofix CIH.
  intros [] Hfin.
  - by contradict Hfin; constructor.
  - apply Forall_delay, CIH; [done |].
    by contradict Hfin; constructor.
Qed.

(** ** Final element properties *)

Inductive finalT : trace -> A -> Prop :=
| finalT_nil : forall a,
   finalT (Tnil a) a
| finalT_delay : forall a a' tr,
   finalT tr a' ->
   finalT (Tcons a tr) a'.

Lemma finalTA_finiteT : forall tr a, finalT tr a -> finiteT tr.
Proof. by induction 1; constructor. Qed.

Fixpoint final (tr : trace) (h : finiteT tr) {struct h} : A :=
  match tr as tr' return (finiteT tr' -> A) with
  | Tnil a => fun _ => a
  | Tcons a tr => fun h => final tr (invert_finiteT_delay a tr h)
  end h.

Lemma finiteT_finalT : forall tr (h : finiteT tr),
  finalT tr (final tr h).
Proof.
  refine (fix IH tr h {struct h} := _).
  dependent destruction h; subst; [by constructor |].
  by constructor; cbn; apply IH.
Qed.

Fixpoint lengthT (tr : trace) (h : finiteT tr) {struct h} : nat :=
  match tr as tr' return (finiteT tr' -> nat) with
  | Tnil a => fun _ => (S 0)
  | Tcons a tr => fun h => S (lengthT tr (invert_finiteT_delay a tr h))
  end h.

Inductive contains : trace -> A -> Prop :=
| contains_now : forall tr a, hd tr = a -> contains tr a
| contains_delay : forall tr a a', contains tr a -> contains (Tcons a' tr) a.

Fixpoint nth_option (tr : trace) (n : nat) : option A :=
  match n, tr with
  | 0, _ => Some (hd tr)
  | S n', Tcons _ tr' => nth_option tr' n'
  | _, _ => None
  end.

Lemma nth_option_contains : forall (tr : trace) (n : nat) (a : A),
  nth_option tr n = Some a -> contains tr a.
Proof.
  intros tr n a; revert tr; induction n; inversion 1; [by apply contains_now |].
  destruct tr; [done |].
  by apply contains_delay, IHn.
Qed.

Lemma contains_nth_option : forall (tr : trace) (a : A),
  contains tr a <-> exists n, nth_option tr n = Some a.
Proof.
  split.
  - induction 1.
    + by exists 0; cbn; congruence.
    + destruct IHcontains as [n Hn].
      by exists (S n).
  - by intros [n Hn]; eapply nth_option_contains.
Qed.

Lemma nth_keep_nil_option : forall (tr : trace) (n : nat) (a : A),
  nth_option tr n = Some a -> nth_keep_nil tr n = a.
Proof.
  intros tr n a; revert tr; induction n; [by inversion 1 |].
  intros []; [done |]; cbn.
  by rewrite nth_keep_nil_cons; apply IHn.
Qed.

Lemma nth_keep_nil_contains : forall (tr : trace) (n : nat) (a : A),
  nth_keep_nil tr n = a -> contains tr a.
Proof.
  intros tr n a; revert tr; induction n; [by inversion 1; apply contains_now |].
  intros [].
  - by rewrite nth_keep_nil_nil; intros ->; apply contains_now.
  - rewrite nth_keep_nil_cons.
    by intros; apply contains_delay, IHn.
Qed.

Lemma contains_nth_keep_nil : forall (tr : trace) (a : A),
  contains tr a <-> exists n, nth_keep_nil tr n = a.
Proof.
  split.
  - rewrite contains_nth_option.
    intros [n Hn]; exists n.
    by apply nth_keep_nil_option.
  - by intros [n Hn]; eapply nth_keep_nil_contains.
Qed.

End sec_trace_properties.
