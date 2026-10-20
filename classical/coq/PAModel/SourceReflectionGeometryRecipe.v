(** The exact existsK existsbeta geometry statement, retaining arbitrary internally finite pieces. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceRecursionShiftGraphs
 SourceReflectionGeometryPoint SourceReflectionGeometryPointTransport SourcePieceConjunctionBounds.
Unset Implicit Arguments.
Definition source_reflection_geometry_recipe M domain level sb sc count a out:=exists body inner,
 source_reflection_geometry_point M domain level sb sc count(succM M(succM M a))(code_numeral M 1)(zeroM M)body /\
 sf_relation M SFEx body(zeroM M)inner /\sf_relation M SFEx inner(zeroM M)out.
Theorem source_reflection_geometry_recipe_total M domain level sb sc count a:
 exists out,source_reflection_geometry_recipe M domain level sb sc count a out.
Proof.
 destruct(source_reflection_geometry_point_total M domain level sb sc count(succM M(succM M a))(code_numeral M 1)(zeroM M))as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(inner&HI).
 destruct(sf_relation_total M SFEx inner(zeroM M))as(out&HO). exists out,body,inner. auto.
Qed.
Theorem source_reflection_geometry_recipe_functional M domain level sb sc count a x y:
 source_reflection_geometry_recipe M domain level sb sc count a x ->source_reflection_geometry_recipe M domain level sb sc count a y ->x=y.
Proof.
 intros(body&inner&HB&HI&HX)(body'&inner'&HB'&HI'&HY).
 assert(E:body'=body)by(eapply source_reflection_geometry_point_functional;eassumption). subst body'.
 assert(E:inner'=inner)by(eapply sf_relation_functional;eassumption). subst inner'.
 exact(sf_relation_functional M SFEx inner(zeroM M)x y HX HY).
Qed.
Theorem source_reflection_geometry_recipe_bounded M domain level sb sc count a out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->coding_lt M a k ->
 source_reflection_geometry_recipe M domain level sb sc count a out ->source_bounded M out k.
Proof.
 intros HD HL HV BA(body&inner&HB&HI&HO).
 apply(proj2(source_bounded_accept_unary M SFEx inner out k(or_intror eq_refl)HO)).
 apply(proj2(source_bounded_accept_unary M SFEx body inner(succM M k)(or_intror eq_refl)HI)).
 apply(source_reflection_geometry_point_bounded M domain level sb sc count(succM M(succM M a))(code_numeral M 1)(zeroM M)body(succM M(succM M k))HD HL HV).
 - apply(proj2(coding_lt_succ_cancel M(succM M a)(succM M k))),(proj2(coding_lt_succ_cancel M a k));exact BA.
 - apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k)));apply coding_zero_lt_succ.
 - apply coding_zero_lt_succ.
 - exact HB.
Qed.
Theorem source_reflection_geometry_recipe_substitution M domain level sb sc count a old a' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_recipe M domain level sb sc count a old ->source_reflection_geometry_recipe M domain level sb sc count a' new ->
 substitution_lookup M rb rc rn base a a' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HL HV(body&inner&HB&HI&HO)(body'&inner'&HB'&HI'&HO')HA.
 destruct(substitution_lift_total M rb rc rn base)as(b1&c1&n1&H1).
 destruct(substitution_lift_total M b1 c1 n1(succM M base))as(b2&c2&n2&H2).
 apply(proj2(numerical_substitution_quantifier M false inner old rb rc rn base new HO)). exists b1,c1,n1,inner'. split;[exact H1|]. split;[|exact HO'].
 apply(proj2(numerical_substitution_quantifier M false body inner b1 c1 n1(succM M base)inner' HI)). exists b2,c2,n2,body'. split;[exact H2|]. split;[|exact HI'].
 exact(source_reflection_geometry_point_substitution M domain level sb sc count(succM M(succM M a))(code_numeral M 1)(zeroM M)body
  (succM M(succM M a'))(code_numeral M 1)(zeroM M)body' b2 c2 n2(succM M(succM M base))HD HL HV HB HB'
  (proj2(proj2 H2)(succM M a)(succM M a')(proj2(proj2 H1)a a' HA))
  (proj2(proj2 H2)(zeroM M)(zeroM M)(proj1(proj2 H1)))(proj1(proj2 H2))).
Qed.
Theorem source_reflection_geometry_recipe_shift M domain level sb sc count a old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_recipe M domain level sb sc count a old ->source_reflection_geometry_recipe M domain level sb sc count(succM M a)new ->source_formula_shift M old new.
Proof.
 intros HD HL HV HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_reflection_geometry_recipe_substitution M domain level sb sc count a old(succM M a)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HL HV HO HN(source_rec_shift_lookup M a)).
Qed.
Print Assumptions source_reflection_geometry_recipe_total.
Print Assumptions source_reflection_geometry_recipe_functional.
Print Assumptions source_reflection_geometry_recipe_bounded.
Print Assumptions source_reflection_geometry_recipe_substitution.
Print Assumptions source_reflection_geometry_recipe_shift.
