(** The genuine closure witness for the least-Cond reflection relation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded FixedSourceBounds
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceReflectionStep SourceReflectionRecursionKernel
 SourceRecursionTotalRelation SourceRecursionFunctionality SourceRecursionClosureExists SourceRecursionOmegaClosure
 SourceFiniteTelescope SourceFiniteTelescopeZFRApply SourceFiniteNameParameters RenamingSubstitution
 SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_zfr_reflection_closure_zero M level sb sc n matrix target:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
 source_reflection_step M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix ->
 source_rec_closure_exists M matrix(zeroM M)target ->source_zfr_provable M target.
Proof.
 intros HLevel HV HM HT.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_step_bounded M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix(code_numeral M 2)
  (numerical_L_domain_bounded M)HL HV(coding_zero_lt_succ M(code_numeral M 1))(coding_lt_succ M(code_numeral M 1))HM)as BP.
 destruct(source_rec_functionality_total M matrix)as(funlaw&HFun).
 destruct(source_rec_total_relation_total M matrix)as(totalG&HG).
 pose proof(source_zfr_reflection_rec_functional M level sb sc n matrix funlaw HLevel HV HM HFun)as PFun.
 pose proof(source_zfr_reflection_rec_total M level sb sc n matrix totalG HLevel HV HM HG)as PG.
 destruct(source_finite_telescope_total M[funlaw;totalG]target)as(law&HLaw).
 pose proof(source_zfr_rec_omega_closure M matrix funlaw totalG target law BP HFun HG HT HLaw)as PLaw.
 apply(source_zfr_finite_telescope_apply M[funlaw;totalG]target law HLaw PLaw).
 intros a[<-|[<-|[]]];assumption.
Qed.
Theorem source_zfr_reflection_closure M level sb sc n matrix a target:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
 source_reflection_step M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix ->
 source_rec_closure_exists M matrix a target ->source_zfr_provable M target.
Proof.
 intros HLevel HV HM HT.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_step_bounded M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix(code_numeral M 2)
  (numerical_L_domain_bounded M)HL HV(coding_zero_lt_succ M(code_numeral M 1))(coding_lt_succ M(code_numeral M 1))HM)as BP.
 destruct(source_rec_closure_exists_total M matrix(zeroM M))as(old&HO).
 pose proof(source_zfr_reflection_closure_zero M level sb sc n matrix old HLevel HV HM HO)as PO.
 destruct(source_finite_names_total M 1(fun _=>a)(zeroM M))as(rb&rc&HNames).
 pose proof(source_rec_closure_exists_substitution M matrix(zeroM M)old a target rb rc(code_numeral M 1)
  (addM M(code_numeral M 1)(zeroM M))BP HO HT
  (proj1(renaming_substitution_lookup M rb rc(code_numeral M 1)(zeroM M)(zeroM M)a)(HNames 0 ltac:(lia))))as HS.
 apply(proj1(source_zfr_descriptor_provable M target)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor old rb rc(code_numeral M 1)(zeroM M)target
  (proj2(source_zfr_descriptor_provable M old)PO)
  (proj2(numerical_renaming_substitution M old rb rc(code_numeral M 1)(zeroM M)target)HS)).
Qed.
Theorem source_zfr_reflection_closure_total M level sb sc n a:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
 exists matrix target,source_reflection_step M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix /\
 source_rec_closure_exists M matrix a target /\source_zfr_provable M target.
Proof.
 intros HL HV.
 destruct(source_reflection_step_total M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1))as(matrix&HM).
 destruct(source_rec_closure_exists_total M matrix a)as(target&HT).
 exists matrix,target. repeat split;try assumption.
 exact(source_zfr_reflection_closure M level sb sc n matrix a target HL HV HM HT).
Qed.
Print Assumptions source_zfr_reflection_closure_zero.
Print Assumptions source_zfr_reflection_closure.
Print Assumptions source_zfr_reflection_closure_total.
