(** Actual two ExI rules for the chosen K,beta geometry witnesses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceSequents SourceQuantifierRules
 NumericalContexts NumericalSourceFull NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource SourceInstantiationConstructors
 SourceReflectionGeometryPoint SourceReflectionGeometryPointTransport SourceReflectionGeometryRecipe SourcePieceConjunctionBounds.
Unset Implicit Arguments.
Theorem source_reflection_geometry_witness_instances M domain level sb sc count a K beta point target:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_point M domain level sb sc count a K beta point ->source_reflection_geometry_recipe M domain level sb sc count a target ->
 exists body inner middle innerMiddle,
 sf_relation M SFEx body(zeroM M)inner /\sf_relation M SFEx inner(zeroM M)target /\
 sf_relation M SFEx middle(zeroM M)innerMiddle /\numerical_instantiation M inner K innerMiddle /\numerical_instantiation M middle beta point.
Proof.
 intros HD HL HV HPoint(body&inner&HB&HI&HT).
 destruct(source_reflection_geometry_point_total M domain level sb sc count(succM M a)(succM M K)(zeroM M))as(middle&HM).
 destruct(sf_relation_total M SFEx middle(zeroM M))as(innerMiddle&HIM).
 exists body,inner,middle,innerMiddle. split;[exact HI|]. split;[exact HT|]. split;[exact HIM|]. split.
 - destruct(substitution_singleton_total M K)as(rb&rc&HHead&_).
   destruct(substitution_lift_total M rb rc(code_numeral M 1)(zeroM M))as(lb&lc&ln&HMap).
   exists rb,rc. split;[exact HHead|].
   apply(proj2(numerical_substitution_quantifier M false body inner rb rc(code_numeral M 1)(zeroM M)innerMiddle HI)). exists lb,lc,ln,middle. split;[exact HMap|]. split;[|exact HIM].
   exact(source_reflection_geometry_point_substitution M domain level sb sc count(succM M(succM M a))(code_numeral M 1)(zeroM M)body
    (succM M a)(succM M K)(zeroM M)middle lb lc ln(code_numeral M 1)HD HL HV HB HM
    (proj2(proj2 HMap)(succM M a)a(substitution_singleton_tail M rb rc a))
    (proj2(proj2 HMap)(zeroM M)K HHead)(proj1(proj2 HMap))).
 - destruct(substitution_singleton_total M beta)as(rb&rc&HHead&_).
   exists rb,rc. split;[exact HHead|].
   exact(source_reflection_geometry_point_substitution M domain level sb sc count(succM M a)(succM M K)(zeroM M)middle a K beta point
    rb rc(code_numeral M 1)(zeroM M)HD HL HV HM HPoint(substitution_singleton_tail M rb rc a)(substitution_singleton_tail M rb rc K)HHead).
Qed.
Theorem source_full_reflection_geometry_witness M b c n domain level sb sc count a K beta point target k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 coding_lt M a k ->context_bounded M b c n k ->source_reflection_geometry_point M domain level sb sc count a K beta point ->
 source_reflection_geometry_recipe M domain level sb sc count a target ->source_full_prv M b c n point ->source_full_prv M b c n target.
Proof.
 intros HD HL HV BA BC HP HT PP.
 destruct(source_reflection_geometry_witness_instances M domain level sb sc count a K beta point target HD HL HV HP HT)
  as(body&inner&middle&innerMiddle&HI&HOuter&HIM&HInstK&HInstBeta).
 assert(HWF:source_sequent_wf M b c n target).
 { exists k. split;[exact(source_reflection_geometry_recipe_bounded M domain level sb sc count a target k HD HL HV BA HT)|exact BC]. }
 pose proof(source_wf_quantifier_instance M b c n SFEx inner target K innerMiddle(or_intror eq_refl)HOuter HWF HInstK)as HMiddleWF.
 pose proof(full_source_ExI M b c n middle innerMiddle beta point HMiddleWF PP HIM HInstBeta)as PMiddle.
 exact(full_source_ExI M b c n inner target K innerMiddle HWF PMiddle HOuter HInstK).
Qed.
Print Assumptions source_reflection_geometry_witness_instances.
Print Assumptions source_full_reflection_geometry_witness.
