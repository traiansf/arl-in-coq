From stdpp Require Import prelude fin_maps.
From ARL.Lib Require Import Lists.

Section refresh_map.

Context
  `{Infinite K, FinSet K KSet}.

Fixpoint refresh_list'
    (orig : list K) (X : KSet) : list (K * K) :=
  match orig with
  | [] => []
  | x :: orig => let x' := fresh X in (x, x') :: refresh_list' orig ({[ x' ]} ∪ X)
  end.

Definition refresh_list (to_rename to_avoid : KSet) : list (K * K) :=
  refresh_list' (elements to_rename) (to_avoid ∪ to_rename).

Lemma refresh_list_replacements_are_fresh' (orig : list K) (X : KSet) P `{forall xy, Decision (P xy)}:
  forall y, y ∈ (map snd (filter P (refresh_list' orig X))) -> y ∉ X.
Proof.
  revert X; induction orig; [by inversion 1 | ].
  intros ? ?; rewrite elem_of_list_fmap; intros (xy & -> & Hfilter).
  apply elem_of_list_filter in Hfilter as [Hp Hxy]; cbn in Hxy.
  apply elem_of_cons in Hxy as [-> | Hy].
  - by apply is_fresh.
  - apply not_elem_of_union with (X := {[fresh X]}),
      IHorig, elem_of_list_fmap.
    eexists; split; [done |].
    by apply elem_of_list_filter.
Qed.

Lemma refresh_list_replacements_nodup' :
  forall orig X P `{forall xy, Decision (P xy)},
    NoDup (map snd (filter P (refresh_list' orig X))).
Proof.
  induction orig; [by constructor |]; cbn; intros.
  case_decide; [| by apply IHorig].
  constructor; [| by apply IHorig].
  intro Hx; apply refresh_list_replacements_are_fresh' in Hx.
  by contradict Hx; rewrite elem_of_union, elem_of_singleton; left.
Qed.

Lemma refresh_list_replacements_nodup :
  forall orig X P `{forall xy, Decision (P xy)},
    NoDup (map snd (filter P (refresh_list orig X))).
Proof.
  by intros orig X; apply refresh_list_replacements_nodup'.
Qed.

Lemma refresh_list_fst' :
  forall orig X, map fst (refresh_list' orig X) = orig.
Proof.
  induction orig; [done |]; cbn.
  by intro X; f_equal; apply IHorig.
Qed.

Lemma refresh_list_fst :
  forall orig X, map fst (refresh_list orig X) = elements orig.
Proof. by intros; apply refresh_list_fst'. Qed.

Lemma refresh_list_nodup :
  forall orig X, NoDup (map fst (refresh_list orig X) ++ map snd (refresh_list orig X)).
Proof.
  intros.
  apply NoDup_app; split_and!.
  - by rewrite refresh_list_fst; apply NoDup_elements.
  - intro x; rewrite refresh_list_fst, elem_of_elements; intros Hx1 Hx2.
    eapply refresh_list_replacements_are_fresh' with (P := const True);
      [by rewrite list_filter_True |].
    by rewrite elem_of_union; right.
  - rewrite <- (list_filter_True (refresh_list orig X)).
    by apply refresh_list_replacements_nodup.
Qed.

Lemma refresh_list_replacements_orig :
  forall orig X P `{forall xy, Decision (P xy)},
    list_to_set (map snd (filter P (refresh_list orig X))) ## orig.
Proof.
  intros.
  pose proof (Hnodup := refresh_list_nodup orig X).
  apply NoDup_app in Hnodup as (_ & Hnodup & _).
  intros x Hrepl Horig.
  apply (Hnodup x).
  - by rewrite refresh_list_fst, elem_of_elements.
  - apply elem_of_list_to_set, elem_of_list_fmap in Hrepl
      as (xy & -> & Hxy).
    apply elem_of_list_fmap; eexists; split; [done |].
    by apply elem_of_list_filter in Hxy as [].
Qed.

Lemma refresh_list_replacements_avoid (orig X : KSet) P `{forall xy, Decision (P xy)} :
  list_to_set (map snd (filter P (refresh_list orig X))) ## X.
Proof.
  intro y; rewrite elem_of_list_to_set; intro Hy.
  apply refresh_list_replacements_are_fresh' in Hy.
  by contradict Hy; apply elem_of_union; left.
Qed.

End refresh_map.
