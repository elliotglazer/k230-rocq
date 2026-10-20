(** Actual arbitrary-code substitution into witness_theta. The quantified
    matrix uses the genuine lifted substitution. In particular the diagonal
    and positive-selector instances are not obtained by textual renaming. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes NumericalSubstitutionMaps
  NumericalSubstitution SourceWitnessThetaRecipe SourcePropositionalTemplates
  SourceReflectedExistential SourceReflectionSelectors SourceRelativizedSelectors.
Unset Implicit Arguments.

Theorem source_witness_theta_substitution_selector M phi theta eb ec en base out s t :
  source_witness_theta_recipe M phi theta ->numerical_substitution M theta eb ec en base out ->
  substitution_lookup M eb ec en base (code_numeral M 2) s ->
  substitution_lookup M eb ec en base (code_numeral M 3) t ->
  exists a b aout lb lc ln bout some test,
    source_witness_theta_matrix M false phi a /\source_witness_theta_matrix M true phi b /\
    numerical_substitution M a eb ec en base aout /\
    substitution_lift M eb ec en base lb lc ln /\
    numerical_substitution M b lb lc ln (succM M base) bout /\
    sf_relation M SFEx bout (zeroM M) some /\sf_relation M SFMember s t test /\
    source_selector_graph M test aout some out.
Proof.
  intros(a&b&g&negative&oldSome&left&right&HA&HB&HG&HN&HE&HL&HR&HO) HS HSName HTName.
  destruct(proj1(numerical_substitution_binary M SFOr left right theta eb ec en base out
    (or_intror(or_introl eq_refl)) HO) HS) as(left'&right'&HSLeft&HSRight&HOr).
  destruct(proj1(numerical_substitution_binary M SFAnd g a left eb ec en base left'
    (or_introl eq_refl) HL) HSLeft) as(test&aout&HSTest&HSAout&HAndLeft).
  destruct(proj1(numerical_substitution_binary M SFAnd negative oldSome right eb ec en base right'
    (or_introl eq_refl) HR) HSRight) as(negative'&some&HSNeg&HSSome&HAndRight).
  destruct(proj1(numerical_substitution_member M (code_numeral M 2)(code_numeral M 3) g
    eb ec en base test HG) HSTest) as(s'&t'&HS'&HT'&HTest).
  pose proof(substitution_lookup_functional M eb ec en base _ s' s HS' HSName) as ES. subst s'.
  pose proof(substitution_lookup_functional M eb ec en base _ t' t HT' HTName) as ET. subst t'.
  destruct(proj1(numerical_substitution_binary M SFImpl g (zeroM M) negative eb ec en base negative'
    (or_intror(or_intror eq_refl)) HN) HSNeg) as(test'&falsity&HSGuard&HSFalse&HNeg).
  pose proof(numerical_substitution_functional M g eb ec en base test' test HSGuard HSTest) as EG. subst test'.
  apply(proj1(numerical_substitution_invalid M (zeroM M) eb ec en base falsity (or_introl eq_refl))) in HSFalse.
  subst falsity.
  destruct(proj1(numerical_substitution_quantifier M false b oldSome eb ec en base some HE) HSSome)
    as(lb&lc&ln&bout&HMap&HSBout&HEx).
  exists a,b,aout,lb,lc,ln,bout,some,test.
  split;[exact HA|]. split;[exact HB|]. split;[exact HSAout|]. split;[exact HMap|].
  split;[exact HSBout|]. split;[exact HEx|]. split;[exact HTest|].
  unfold source_selector_graph,source_reflection_pair_left,source_selector.
  apply(source_prop_template_join M (source_reflection_five_env test aout some aout some) SFOr
    (SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTAnd(SPTImpl(SPTSlot 0) SPTFalse)(SPTSlot 2))
    left' right' out);[| |exact HOr].
  - exact(source_prop_template_join M (source_reflection_five_env test aout some aout some) SFAnd
      (SPTSlot 0)(SPTSlot 1) test aout left' eq_refl eq_refl HAndLeft).
  - apply(source_prop_template_join M (source_reflection_five_env test aout some aout some) SFAnd
      (SPTImpl(SPTSlot 0) SPTFalse)(SPTSlot 2) negative' some right');[|reflexivity|exact HAndRight].
    exact(source_prop_template_join M (source_reflection_five_env test aout some aout some) SFImpl
      (SPTSlot 0) SPTFalse test (zeroM M) negative' eq_refl eq_refl HNeg).
Qed.

Print Assumptions source_witness_theta_substitution_selector.
