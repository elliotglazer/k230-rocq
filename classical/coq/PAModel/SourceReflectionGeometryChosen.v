(** Actual geometry recipe at chosen ordinal-family and union witnesses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
 NumericalContexts NumericalSourceFull SourceFiniteTelescope SourceZFRFiniteRule SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds
 SourceOrdinalPredicate SourceDomainInstances SourceRecursionClosureSyntax SourceRecursionPrimitiveRelations SourceReflectionStep
 SourceReflectionOrdinalChart SourceReflectionGeometryPredicates SourceReflectionGeometryPoint SourceReflectionGeometryPointProof
 SourceReflectionGeometryRecipe SourceReflectionGeometryWitness SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_geometry_chosen M level sb sc count phi a Y K beta chart closure ordA union target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->coding_lt M beta k ->
 source_reflection_ordinal_chart M Y K chart ->source_rec_closure M phi a Y closure ->numerical_instantiation M(source_ordinal_predicate_code M)a ordA ->
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union ->
 source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc count a target ->
 source_finite_telescope M[chart;closure;ordA;union]target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HM BA BY BK BB HC HClosure HOA HU HT HLaw.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 destruct(source_reflection_geometry_point_total M(source_L_domain_code M)level sb sc count a K beta)as(point&HP).
 destruct(source_finite_telescope_total M[chart;closure;ordA;union]point)as(pointLaw&HPointLaw).
 pose proof(source_zfr_reflection_geometry_point M level sb sc count phi a Y K beta chart closure ordA union point pointLaw k
  HLevel HV BP HM BA BY BK BB HC HClosure HOA HU HP HPointLaw)as PPointLaw.
 pose proof(source_reflection_ordinal_chart_bounded M Y K chart k BY BK HC)as BC.
 pose proof(source_rec_closure_bounded M phi a Y closure k BP BA BY HClosure)as BClosure.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)a ordA k(source_ordinal_predicate_bounded M)BA HOA)as BO.
 pose proof(source_reflection_geometry_instance_bounded M ReflectionUnion(source_rec_env2 K beta)union k ltac:(intros[|i]HI;[exact BK|exact BB])HU)as BU.
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc count a target k(numerical_L_domain_bounded M)HL HV BA HT)as BT.
 apply(source_zfr_finite_rule M[pointLaw][chart;closure;ordA;union]target law k).
 - intros f[<-|[<-|[<-|[<-|[]]]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros f[<-|[]]. exact PPointLaw.
 - intros b c n BContext Laws Premises.
   pose proof(source_full_finite_telescope_apply M[chart;closure;ordA;union]point pointLaw HPointLaw b c n(Laws pointLaw(or_introl eq_refl))Premises)as PPoint.
   exact(source_full_reflection_geometry_witness M b c n(source_L_domain_code M)level sb sc count a K beta point target k
    (numerical_L_domain_bounded M)HL HV BA BContext HP HT PPoint).
Qed.
Print Assumptions source_zfr_reflection_geometry_chosen.
