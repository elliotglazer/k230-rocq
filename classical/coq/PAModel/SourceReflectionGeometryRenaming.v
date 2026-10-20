(** Actual arbitrary finite-prefix renaming of geometry and hierarchy graphs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceHierarchySyntax SourceReflectionGeometryPoint SourceReflectionGeometryPointTransport SourcePieceConjunctionBounds
 NumericalRenamingMaps NumericalRenaming RenamingSubstitution.
Unset Implicit Arguments.
Theorem source_LL_instance_renaming M beta Lb old beta' Lb' new rb rc rn delta:
 source_LL_instance M beta Lb old ->source_LL_instance M beta' Lb' new ->
 renaming_lookup M rb rc rn delta beta beta' ->renaming_lookup M rb rc rn delta Lb Lb' ->
 numerical_renaming M old rb rc rn delta new.
Proof.
 intros HO HN HB HL. apply(proj2(numerical_renaming_substitution M old rb rc rn delta new)).
 exact(source_LL_instance_substitution M beta Lb old beta' Lb' new rb rc rn(addM M rn delta)HO HN
  (proj1(renaming_substitution_lookup M rb rc rn delta beta beta')HB)
  (proj1(renaming_substitution_lookup M rb rc rn delta Lb Lb')HL)).
Qed.
Theorem source_LL_instance_shift_by M beta Lb old params new:
 source_LL_instance M beta Lb old ->source_LL_instance M(addM M beta params)(addM M Lb params)new ->
 numerical_renaming M old(zeroM M)(zeroM M)(zeroM M)params new.
Proof.
 intros HO HN. apply(source_LL_instance_renaming M beta Lb old(addM M beta params)(addM M Lb params)new
  (zeroM M)(zeroM M)(zeroM M)params HO HN);right;split;try apply coding_not_lt_zero;reflexivity.
Qed.
Theorem source_reflection_geometry_point_renaming M domain level sb sc count a K beta old a' K' beta' new rb rc rn delta:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_point M domain level sb sc count a K beta old ->source_reflection_geometry_point M domain level sb sc count a' K' beta' new ->
 renaming_lookup M rb rc rn delta a a' ->renaming_lookup M rb rc rn delta K K' ->renaming_lookup M rb rc rn delta beta beta' ->
 numerical_renaming M old rb rc rn delta new.
Proof.
 intros HD HL HV HO HN HA HK HB. apply(proj2(numerical_renaming_substitution M old rb rc rn delta new)).
 exact(source_reflection_geometry_point_substitution M domain level sb sc count a K beta old a' K' beta' new rb rc rn(addM M rn delta)
  HD HL HV HO HN(proj1(renaming_substitution_lookup M rb rc rn delta a a')HA)
  (proj1(renaming_substitution_lookup M rb rc rn delta K K')HK)(proj1(renaming_substitution_lookup M rb rc rn delta beta beta')HB)).
Qed.
Theorem source_reflection_geometry_point_shift_by M domain level sb sc count a K beta old params new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_point M domain level sb sc count a K beta old ->
 source_reflection_geometry_point M domain level sb sc count(addM M a params)(addM M K params)(addM M beta params)new ->
 numerical_renaming M old(zeroM M)(zeroM M)(zeroM M)params new.
Proof.
 intros HD HL HV HO HN. apply(source_reflection_geometry_point_renaming M domain level sb sc count a K beta old
  (addM M a params)(addM M K params)(addM M beta params)new(zeroM M)(zeroM M)(zeroM M)params HD HL HV HO HN);
 right;split;try apply coding_not_lt_zero;reflexivity.
Qed.
Print Assumptions source_LL_instance_renaming.
Print Assumptions source_LL_instance_shift_by.
Print Assumptions source_reflection_geometry_point_renaming.
Print Assumptions source_reflection_geometry_point_shift_by.
