From stdpp Require Import prelude fin_maps.

Section refresh_map.

Context
  `{Infinite K}
  `{FinMap K M}.

Fixpoint refresh_map' `{Fresh K C, Union C, Singleton K C}
    (orig : list K) (X : C) : M K :=
  match orig with
  | [] => empty
  | x :: orig => let x' := fresh X in insert x x' (refresh_map' orig ({[ x' ]} ∪ X))
  end.

Definition refresh_map `{Fresh K C, FinSet K C} (orig : list K) (X : C) : M K :=
  refresh_map' orig (X ∪ list_to_set orig).

End refresh_map.
