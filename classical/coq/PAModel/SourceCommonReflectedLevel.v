(** Literal existence of a single L-level containing the internally finite
    parameter block and reflecting an independently bounded source matrix. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceCommonLevelPoint SourceCommonLevelWitness SourceOrdinaryReflectionSyntax
 SourceOrdinaryReflectionTransport SourceLFixed NumericalSubstitutionMaps NumericalSubstitution.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Definition source_common_reflected_level_point M start paramCount reflectCount phi beta Y out:=exists common refl,
 source_common_level_point M start paramCount beta Y common /\
 source_ordinary_reflection M(source_L_domain_code M)reflectCount phi beta refl /\
 sf_relation M SFAnd common refl out.
Definition source_common_reflected_level_recipe M start paramCount reflectCount phi out:=exists point inner,
 source_common_reflected_level_point M(succM M(succM M start))paramCount reflectCount phi
  (code_numeral M 1)(zeroM M)point /\
 sf_relation M SFEx point(zeroM M)inner /\sf_relation M SFEx inner(zeroM M)out.
Theorem source_common_reflected_level_point_total M start paramCount reflectCount phi beta Y:
 exists out,source_common_reflected_level_point M start paramCount reflectCount phi beta Y out.
Proof.
 destruct(source_common_level_point_total M start paramCount beta Y)as(common&HCommon).
 destruct(source_ordinary_reflection_total M(source_L_domain_code M)reflectCount phi beta)as(refl&HRefl).
 destruct(sf_relation_total M SFAnd common refl)as(out&HOut).
 exists out,common,refl. auto.
Qed.
Theorem source_common_reflected_level_recipe_total M start paramCount reflectCount phi:
 exists out,source_common_reflected_level_recipe M start paramCount reflectCount phi out.
Proof.
 destruct(source_common_reflected_level_point_total M(succM M(succM M start))paramCount reflectCount phi
  (code_numeral M 1)(zeroM M))as(point&HPoint).
 destruct(sf_relation_total M SFEx point(zeroM M))as(inner&HInner).
 destruct(sf_relation_total M SFEx inner(zeroM M))as(out&HOut).
 exists out,point,inner. auto.
Qed.
Theorem source_common_reflected_level_point_bounded M start paramCount reflectCount phi beta Y out k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->
 coding_lt M beta k ->coding_lt M Y k ->source_common_reflected_level_point M start paramCount reflectCount phi beta Y out ->
 source_bounded M out k.
Proof.
 intros BF HNames BB BY(common&refl&HCommon&HRefl&HOut).
 apply(proj2(source_bounded_accept_binary M SFAnd common refl out k(or_introl eq_refl)HOut)). split.
 - exact(source_common_level_point_bounded M start paramCount beta Y common k HNames BB BY HCommon).
 - exact(source_ordinary_reflection_bounded M(source_L_domain_code M)reflectCount phi beta refl k
   (numerical_L_domain_bounded M)BF BB HRefl).
Qed.
Theorem source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi out k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi out ->source_bounded M out k.
Proof.
 intros BF HNames(point&inner&HPoint&HInner&HOut).
 apply(proj2(source_bounded_accept_unary M SFEx inner out k(or_intror eq_refl)HOut)).
 apply(proj2(source_bounded_accept_unary M SFEx point inner(succM M k)(or_intror eq_refl)HInner)).
 apply(source_common_reflected_level_point_bounded M(succM M(succM M start))paramCount reflectCount phi
   (code_numeral M 1)(zeroM M)point(succM M(succM M k))BF).
 - intros i HI. rewrite !source_common_add_successor.
   apply(proj2(coding_lt_succ_cancel M(succM M(addM M i start))(succM M k))).
   exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HNames i HI)).
 - change(coding_lt M(succM M(zeroM M))(succM M(succM M k))).
   apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))). apply coding_zero_lt_succ.
 - apply coding_zero_lt_succ.
 - exact HPoint.
Qed.
Theorem source_common_reflected_level_point_substitution M start paramCount reflectCount phi beta Y old
 start' beta' Y' new b c n base:
 source_bounded M phi reflectCount ->
 source_common_reflected_level_point M start paramCount reflectCount phi beta Y old ->
 source_common_reflected_level_point M start' paramCount reflectCount phi beta' Y' new ->
 substitution_lookup M b c n base beta beta' ->substitution_lookup M b c n base Y Y' ->
 (forall i,coding_lt M i paramCount ->substitution_lookup M b c n base(addM M i start)(addM M i start')) ->
 numerical_substitution M old b c n base new.
Proof.
 intros BF(common&refl&HCommon&HRefl&HOut)(common'&refl'&HCommon'&HRefl'&HOut')HB HY HNames.
 apply(proj2(numerical_substitution_binary M SFAnd common refl old b c n base new(or_introl eq_refl)HOut)).
 exists common',refl'. split.
 - exact(source_common_level_point_substitution M start paramCount beta Y common start' beta' Y' common'
    b c n base HCommon HCommon' HB HY HNames).
 - split;[|exact HOut'].
   exact(source_ordinary_reflection_substitution M(source_L_domain_code M)reflectCount phi beta refl beta' refl'
    b c n base(numerical_L_domain_bounded M)BF HRefl HRefl' HB).
Qed.
Print Assumptions source_common_reflected_level_point_total.
Print Assumptions source_common_reflected_level_recipe_total.
Print Assumptions source_common_reflected_level_point_bounded.
Print Assumptions source_common_reflected_level_recipe_bounded.
Print Assumptions source_common_reflected_level_point_substitution.
