(** Discharge the genuine ordinal-subcarrier Separation witness. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopeRemoveTheorem SourceFiniteTelescopePermutation
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceOrdinalPredicate SourceDomainInstances SourceDomainChosenShift
 SourceRecursionClosureSyntax SourceRecursionClosureTransport SourceRecursionExAAdjoin
 SourceReflectionStep SourceReflectionOrdinalChart SourceReflectionOrdinalSeparation SourceReflectionGeometryRecipe SourceReflectionGeometryUnion SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_geometry_from_closure M level sb sc count phi a Y closure ordA target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->source_rec_closure M phi a Y closure ->numerical_instantiation M(source_ordinal_predicate_code M)a ordA ->
 source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc count a target ->
 source_finite_telescope M[closure;ordA]target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HM BA BY HClosure HOA HT HLaw. set(s:=succM M).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_rec_closure_bounded M phi a Y closure k BP BA BY HClosure)as BF.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)a ordA k(source_ordinal_predicate_bounded M)BA HOA)as BO.
 assert(Bounds:forall f,In f[closure;ordA]->source_bounded M f k)by(intros f[<-|[<-|[]]];assumption).
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc count a target k(numerical_L_domain_bounded M)HL HV BA HT)as BT.
 destruct(source_zfr_reflection_ordinal_separation M Y)as(body&ex&HBody&HEx&PEx).
 pose proof(source_reflection_ordinal_chart_bounded M(s Y)(zeroM M)body(s k)(proj2(coding_lt_succ_cancel M Y k)BY)(coding_zero_lt_succ M k)HBody)as BBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)BBody)as BEx.
 destruct(source_rec_closure_total M phi(s a)(s Y))as(closureS&HFS).
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(s a))as(ordAS&HOS).
 assert(HS:Forall2(SourceQuantifierRules.source_formula_shift M)[closure;ordA][closureS;ordAS]).
 { constructor;[exact(source_rec_closure_shift M phi a Y closure closureS BP HClosure HFS)|].
   constructor;[exact(source_domain_instance_chosen_shift M(source_ordinal_predicate_code M)a ordA ordAS(source_ordinal_predicate_bounded M)HOA HOS)|constructor]. }
 destruct(source_reflection_geometry_recipe_total M(source_L_domain_code M)level sb sc count(s a))as(targetS&HTS).
 pose proof(source_reflection_geometry_recipe_shift M(source_L_domain_code M)level sb sc count a target targetS(numerical_L_domain_bounded M)HL HV HT HTS)as STarget.
 destruct(source_finite_telescope_total M[body;closureS;ordAS]targetS)as(oldBranch&HOldBranch).
 assert(POldBranch:source_zfr_provable M oldBranch).
 { apply(source_zfr_reflection_geometry_from_chart M level sb sc count phi(s a)(s Y)(zeroM M)body closureS ordAS targetS oldBranch(s k)HLevel HV BP HM);
   try(rec_exa_name_bound);assumption. }
 destruct(source_finite_telescope_total M([closureS;ordAS]++[body])targetS)as(branch&HBranch).
 pose proof(source_rec_closure_bounded M phi(s a)(s Y)closureS(s k)BP(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M Y k)BY)HFS)as BFS.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(s a)ordAS(s k)(source_ordinal_predicate_bounded M)(proj2(coding_lt_succ_cancel M a k)BA)HOS)as BOS.
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc count(s a)targetS(s k)(numerical_L_domain_bounded M)HL HV(proj2(coding_lt_succ_cancel M a k)BA)HTS)as BTS.
 pose proof(source_zfr_finite_telescope_inclusion M[body;closureS;ordAS]([closureS;ordAS]++[body])targetS oldBranch branch(s k)
  ltac:(intros f HF;cbn in HF;destruct HF as[<-|[<-|[<-|[]]]];assumption)BTS HOldBranch HBranch
  ltac:(intros f HF;cbn in HF|-*;tauto)POldBranch)as PBranch.
 destruct(source_finite_telescope_total M([closure;ordA]++[ex])target)as(exLaw&HExLaw).
 pose proof(source_zfr_finite_telescope_exists M[closure;ordA][closureS;ordAS]body ex target targetS branch exLaw k
  Bounds BEx BT HS HEx STarget HBranch HExLaw PBranch)as PExLaw.
 exact(source_zfr_finite_telescope_remove_theorem M[closure;ordA]ex target exLaw law k Bounds BT HExLaw HLaw PEx PExLaw).
Qed.
Print Assumptions source_zfr_reflection_geometry_from_closure.
