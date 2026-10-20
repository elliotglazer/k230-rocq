(** Genuine uniform reflection geometry in every PA model.
 The three Clos/Separation/Union witnesses and every intermediate law are discharged. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopeRemoveTheorem SourceFiniteTelescopePermutation
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceOrdinalPredicate SourceDomainInstances SourceDomainChosenShift
 SourceRecursionClosureSyntax SourceRecursionClosureExists SourceRecursionExAAdjoin
 SourceReflectionStep SourceReflectionClosure SourceReflectionGeometryRecipe SourceReflectionGeometryChart SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_geometry_at_bound M level sb sc count a ordA target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->coding_lt M a k ->
 numerical_instantiation M(source_ordinal_predicate_code M)a ordA ->source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc count a target ->
 source_finite_telescope M[ordA]target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BA HOA HT HLaw. set(s:=succM M).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 destruct(source_reflection_step_total M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1))as(phi&HM).
 pose proof(source_reflection_step_bounded M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi(code_numeral M 2)
  (numerical_L_domain_bounded M)HL HV(coding_zero_lt_succ M(code_numeral M 1))(coding_lt_succ M(code_numeral M 1))HM)as BP.
 destruct(source_rec_closure_exists_total M phi a)as(ex&HExGraph).
 pose proof(source_zfr_reflection_closure M level sb sc count phi a ex HLevel HV HM HExGraph)as PEx.
 pose proof(source_rec_closure_exists_bounded M phi a ex k BP BA HExGraph)as BEx.
 destruct HExGraph as(body&HBody&HEx).
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)a ordA k(source_ordinal_predicate_bounded M)BA HOA)as BO.
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc count a target k(numerical_L_domain_bounded M)HL HV BA HT)as BT.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(s a))as(ordAS&HOS).
 pose proof(source_domain_instance_chosen_shift M(source_ordinal_predicate_code M)a ordA ordAS(source_ordinal_predicate_bounded M)HOA HOS)as SOrd.
 destruct(source_reflection_geometry_recipe_total M(source_L_domain_code M)level sb sc count(s a))as(targetS&HTS).
 pose proof(source_reflection_geometry_recipe_shift M(source_L_domain_code M)level sb sc count a target targetS(numerical_L_domain_bounded M)HL HV HT HTS)as STarget.
 destruct(source_finite_telescope_total M[body;ordAS]targetS)as(oldBranch&HOldBranch).
 assert(POldBranch:source_zfr_provable M oldBranch).
 { apply(source_zfr_reflection_geometry_from_closure M level sb sc count phi(s a)(zeroM M)body ordAS targetS oldBranch(s k)HLevel HV BP HM);
   try(rec_exa_name_bound);assumption. }
 destruct(source_finite_telescope_total M([ordAS]++[body])targetS)as(branch&HBranch).
 pose proof(source_rec_closure_bounded M phi(s a)(zeroM M)body(s k)BP(proj2(coding_lt_succ_cancel M a k)BA)(coding_zero_lt_succ M k)HBody)as BBody.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(s a)ordAS(s k)(source_ordinal_predicate_bounded M)(proj2(coding_lt_succ_cancel M a k)BA)HOS)as BOS.
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc count(s a)targetS(s k)(numerical_L_domain_bounded M)HL HV(proj2(coding_lt_succ_cancel M a k)BA)HTS)as BTS.
 pose proof(source_zfr_finite_telescope_inclusion M[body;ordAS]([ordAS]++[body])targetS oldBranch branch(s k)
  ltac:(intros f HF;cbn in HF;destruct HF as[<-|[<-|[]]];assumption)BTS HOldBranch HBranch
  ltac:(intros f HF;cbn in HF|-*;tauto)POldBranch)as PBranch.
 destruct(source_finite_telescope_total M([ordA]++[ex])target)as(exLaw&HExLaw).
 pose proof(source_zfr_finite_telescope_exists M[ordA][ordAS]body ex target targetS branch exLaw k
  ltac:(intros f[<-|[]];exact BO)BEx BT ltac:(constructor;[exact SOrd|constructor])HEx STarget HBranch HExLaw PBranch)as PExLaw.
 exact(source_zfr_finite_telescope_remove_theorem M[ordA]ex target exLaw law k ltac:(intros f[<-|[]];exact BO)BT HExLaw HLaw PEx PExLaw).
Qed.
Theorem source_zfr_reflection_geometry M level sb sc count a ordA target law:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 numerical_instantiation M(source_ordinal_predicate_code M)a ordA ->source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc count a target ->
 source_finite_telescope M[ordA]target law ->source_zfr_provable M law.
Proof.
 intros HL HV HO HT HLaw.
 exact(source_zfr_reflection_geometry_at_bound M level sb sc count a ordA target law(succM M a)HL HV(coding_lt_succ M a)HO HT HLaw).
Qed.
Theorem source_zfr_reflection_geometry_total M level sb sc count a:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 exists ordA target law,numerical_instantiation M(source_ordinal_predicate_code M)a ordA /\
 source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc count a target /\sf_relation M SFImpl ordA target law /\source_zfr_provable M law.
Proof.
 intros HL HV.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)a)as(ordA&HO).
 destruct(source_reflection_geometry_recipe_total M(source_L_domain_code M)level sb sc count a)as(target&HT).
 destruct(sf_relation_total M SFImpl ordA target)as(law&HImpl).
 exists ordA,target,law. split;[exact HO|]. split;[exact HT|]. split;[exact HImpl|].
 apply(source_zfr_reflection_geometry M level sb sc count a ordA target law HL HV HO HT).
 exists target. split;[reflexivity|exact HImpl].
Qed.
Print Assumptions source_zfr_reflection_geometry_at_bound.
Print Assumptions source_zfr_reflection_geometry.
Print Assumptions source_zfr_reflection_geometry_total.
