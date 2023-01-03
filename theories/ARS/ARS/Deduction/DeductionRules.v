From stdpp Require Import prelude.
From sets Require Import Ensemble.
From ARS Require Import Traces TransitionSystem CTL.

Class RuleOfConsequence
  `{TransitionSystem} (R : relation (Ensemble idomain)) :=
  rule_of_consequence : Proper ((⊆) --> (⊆) ==> impl) R.

Class RuleOfDisjunction
  `{TransitionSystem} (R : relation (Ensemble idomain)) :=
  rule_of_disjunction : forall φ1 φ2 ψ, R φ1 ψ -> R φ2 ψ -> R (φ1 ∪ φ2) ψ.

Class RuleOfGeneralization
  `{TransitionSystem} (R : relation (Ensemble idomain)) :=
  rule_of_generalization :
    forall `(φ : qspace -> Ensemble idomain) ψ,
    (forall i, R (φ i) ψ) ->
    R (indexed_union φ) ψ.

Class RuleOfInduction
  `{TransitionSystem} (R : relation (Ensemble idomain)) :=
  rule_of_induction :
    forall
      `{qspace : Type} (* instances of quantifiers *)
      (measure : qspace -> idomain)
      (prec : relation idomain)
      (Hwf : well_founded prec)
      {index}
      (φ : index -> qspace -> Ensemble idomain)
      (ψ : index -> qspace -> Ensemble idomain)
      (Hind : forall q0,
        (forall q, prec (measure q) (measure q0) ->
          forall i, R (φ i q) (ψ i q)) ->
        forall i, R (φ i q0) (ψ i q0)),
      forall i q, R (φ i q) (ψ i q).

Class RuleOfAllPathsSingleStep
  `{TransitionSystem} (R : relation (Ensemble idomain)) :=
  rule_of_all_paths_single_step : forall φ, φ ⊆ reducible -> R φ (transition_image_functor φ).

Class RuleOfOnePathSingleStep
  `{TransitionSystem} (R : relation (Ensemble idomain)) :=
  rule_of_one_path_single_step : forall φ ψ,
    (forall a, a ∈ φ -> exists b, b ∈ ψ /\ transition a b) ->
    R φ ψ.

Class AllPathsAFDeduction
  `{TransitionSystem} (R : relation (Ensemble idomain))
  `{!Reflexive R} `{!Transitive R}
  `{!RuleOfConsequence R}
  `{!RuleOfDisjunction R} `{!RuleOfGeneralization R}
  `{!RuleOfInduction R}
  `{!RuleOfAllPathsSingleStep R}
  .

Class OnePathEFDeduction
  `{TransitionSystem} (R : relation (Ensemble idomain))
  `{!Reflexive R} `{!Transitive R}
  `{!RuleOfConsequence R}
  `{!RuleOfDisjunction R} `{!RuleOfGeneralization R}
  `{!RuleOfInduction R}
  `{!RuleOfOnePathSingleStep R}
  .
