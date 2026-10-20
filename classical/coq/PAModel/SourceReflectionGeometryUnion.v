(** Discharge the actual union witness from the two-witness geometry existence proof. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopeRemoveTheorem
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceOrdinalPredicate SourceDomainInstances SourceDomainChosenShift
 SourceRecursionClosureSyntax SourceRecursionClosureTransport SourceRecursionExAAdjoin SourceRecursionPrimitiveRelations
 SourceReflectionStep SourceReflectionOrdinalChart SourceReflectionOrdinalChartTransport SourceReflectionGeometryPredicates
 SourceReflectionUnionExists SourceReflectionGeometryRecipe SourceReflectionGeometryChosen SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_geometry_from_chart M level sb sc count phi a Y K chart closure ordA target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->source_reflection_ordinal_chart M Y K chart ->source_rec_closure M phi a Y closure ->
 numerical_instantiation M(source_ordinal_predicate_code M)a ordA ->source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc count a target ->
 source_finite_telescope M[chart;closure;ordA]target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HM BA BY BK HC HClosure HOA HT HLaw. set(s:=succM M).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_ordinal_chart_bounded M Y K chart k BY BK HC)as BC.
 pose proof(source_rec_closure_bounded M phi a Y closure k BP BA BY HClosure)as BF.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)a ordA k(source_ordinal_predicate_bounded M)BA HOA)as BO.
 assert(Bounds:forall f,In f[chart;closure;ordA]->source_bounded M f k)by(intros f[<-|[<-|[<-|[]]]];assumption).
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc count a target k(numerical_L_domain_bounded M)HL HV BA HT)as BT.
 destruct(source_zfr_reflection_union_exists M K)as(body&ex&HBody&HEx&PEx).
 assert(BEx:source_bounded M ex k).
 { apply(proj2(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)).
   apply(source_reflection_geometry_instance_bounded M ReflectionUnion(source_rec_env2(s K)(zeroM M))body(s k));[|exact HBody].
   intros[|i]HI;[exact(proj2(coding_lt_succ_cancel M K k)BK)|apply coding_zero_lt_succ]. }
 destruct(source_reflection_ordinal_chart_total M(s Y)(s K))as(chartS&HCS).
 destruct(source_rec_closure_total M phi(s a)(s Y))as(closureS&HFS).
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(s a))as(ordAS&HOS).
 assert(HS:Forall2(SourceQuantifierRules.source_formula_shift M)[chart;closure;ordA][chartS;closureS;ordAS]).
 { constructor;[exact(source_reflection_ordinal_chart_shift M Y K chart chartS HC HCS)|]. constructor;[exact(source_rec_closure_shift M phi a Y closure closureS BP HClosure HFS)|].
   constructor;[exact(source_domain_instance_chosen_shift M(source_ordinal_predicate_code M)a ordA ordAS(source_ordinal_predicate_bounded M)HOA HOS)|constructor]. }
 destruct(source_reflection_geometry_recipe_total M(source_L_domain_code M)level sb sc count(s a))as(targetS&HTS).
 pose proof(source_reflection_geometry_recipe_shift M(source_L_domain_code M)level sb sc count a target targetS(numerical_L_domain_bounded M)HL HV HT HTS)as STarget.
 destruct(source_finite_telescope_total M([chartS;closureS;ordAS]++[body])targetS)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_reflection_geometry_chosen M level sb sc count phi(s a)(s Y)(s K)(zeroM M)chartS closureS ordAS body targetS branch(s k)HLevel HV BP HM);
    try(rec_exa_name_bound);assumption. }
 destruct(source_finite_telescope_total M([chart;closure;ordA]++[ex])target)as(exLaw&HExLaw).
 pose proof(source_zfr_finite_telescope_exists M[chart;closure;ordA][chartS;closureS;ordAS]body ex target targetS branch exLaw k
  Bounds BEx BT HS HEx STarget HBranch HExLaw PBranch)as PExLaw.
 exact(source_zfr_finite_telescope_remove_theorem M[chart;closure;ordA]ex target exLaw law k Bounds BT HExLaw HLaw PEx PExLaw).
Qed.
Print Assumptions source_zfr_reflection_geometry_from_chart.
