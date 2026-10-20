(** Ordinary Refl and LL proofs shift their free ordinal/carrier names;
 the internally many reflected parameters are already bound. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionTransport SourceHierarchySyntax
 NumericalRenamingMaps NumericalRenaming RenamingSubstitution NumericalSubstitutionMaps
 NumericalContexts NumericalContextRenaming NumericalSourceFull SourceProofRenaming SourceQuantifierRules.
Unset Implicit Arguments.
Lemma source_native_shift_lookup M x:
 substitution_lookup M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)x(succM M x).
Proof.
 pose proof(proj1(renaming_substitution_lookup M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)x(succM M x))
  (proj2(context_shift_lookup M x(succM M x))eq_refl))as H.
 now rewrite Arithmetic.add_zero in H.
Qed.
Theorem source_ordinary_reflection_shift M domain count phi beta old new:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi count->
 source_ordinary_reflection M domain count phi beta old->source_ordinary_reflection M domain count phi(succM M beta)new->
 source_formula_shift M old new.
Proof.
 intros HD HP HO HN. apply(proj2(numerical_renaming_empty_substitution M old(zeroM M)(zeroM M)(code_numeral M 1)new)).
 exact(source_ordinary_reflection_substitution M domain count phi beta old(succM M beta)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HP HO HN(source_native_shift_lookup M beta)).
Qed.
Theorem source_full_ordinary_reflection_shift M domain count phi beta carrier refl level gb gc gn sb sc:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi count->
 source_ordinary_reflection M domain count phi beta refl->source_LL_instance M beta carrier level->
 context_shift M gb gc gn sb sc->source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->
 exists reflS levelS,source_ordinary_reflection M domain count phi(succM M beta)reflS /\
 source_LL_instance M(succM M beta)(succM M carrier)levelS /\
 source_full_prv M sb sc gn reflS /\source_full_prv M sb sc gn levelS.
Proof.
 intros HD HP HR HL HS PR PL.
 destruct(source_ordinary_reflection_total M domain count phi(succM M beta))as(reflS&HRS).
 destruct(source_LL_instance_total M(succM M beta)(succM M carrier))as(levelS&HLS).
 exists reflS,levelS. split;[exact HRS|]. split;[exact HLS|]. split.
 - exact(source_full_prv_renaming M gb gc gn refl(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc reflS PR HS
   (source_ordinary_reflection_shift M domain count phi beta refl reflS HD HP HR HRS)).
 - apply(source_full_prv_renaming M gb gc gn level(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc levelS PL HS).
   apply(proj2(numerical_renaming_empty_substitution M level(zeroM M)(zeroM M)(code_numeral M 1)levelS)).
   exact(source_LL_instance_substitution M beta carrier level(succM M beta)(succM M carrier)levelS
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HL HLS
    (source_native_shift_lookup M beta)(source_native_shift_lookup M carrier)).
Qed.
Print Assumptions source_ordinary_reflection_shift.
Print Assumptions source_full_ordinary_reflection_shift.
