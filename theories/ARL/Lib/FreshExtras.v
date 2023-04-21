From stdpp Require Import prelude fin_maps.

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

Lemma refresh_list_replacements_are_fresh' (orig : list K) (X : KSet) :
  forall y, y ∈ (map snd (refresh_list' orig X)) -> y ∉ X.
Proof.
  revert X; induction orig; [by inversion 1 | ].
  cbn; intros ? ?; rewrite elem_of_cons; intros [-> | Hy].
  - by apply is_fresh.
  - apply IHorig in Hy.
    by contradict Hy; apply elem_of_union; right.
Qed.

Lemma refresh_list_replacements_nodup' :
  forall orig X , NoDup (map snd (refresh_list' orig X)).
Proof.
  induction orig; [by constructor |]; cbn.
  constructor; [| by apply IHorig].
  intro Hx; apply refresh_list_replacements_are_fresh' in Hx.
  by contradict Hx; rewrite elem_of_union, elem_of_singleton; left.
Qed.

Lemma refresh_list_replacements_nodup :
  forall orig X, NoDup (map snd (refresh_list orig X)).
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
    eapply refresh_list_replacements_are_fresh'; [done |].
    by rewrite elem_of_union; right.
  - apply refresh_list_replacements_nodup.
Qed.

Lemma refresh_list_replacements_orig :
  forall orig X, list_to_set (map snd (refresh_list orig X)) ## orig.
Proof.
  intros.
  pose proof (Hnodup := refresh_list_nodup orig X).
  apply NoDup_app in Hnodup as (_ & Hnodup & _).
  intros x Hrepl Horig.
  apply (Hnodup x).
  - by rewrite refresh_list_fst, elem_of_elements.
  - by apply elem_of_list_to_set in Hrepl.
Qed.

Lemma refresh_list_replacements_avoid (orig X : KSet) :
  list_to_set (map snd (refresh_list orig X)) ## X.
Proof.
  intro y; rewrite elem_of_list_to_set; intro Hy.
  apply refresh_list_replacements_are_fresh' in Hy.
  by contradict Hy; apply elem_of_union; left.
Qed.

End refresh_map.
