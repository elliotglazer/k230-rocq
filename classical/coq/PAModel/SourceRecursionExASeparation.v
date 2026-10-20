(** Actual internally generated Separation for the attempt-existence predicate. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceRecursionPrimitiveRelations SourceRecursionExistsAttempt SourceRecursionExACutoff SourceRecursionExASubset
 SourceZFRProvability SourceZFRSeparationContainer SourceSeparationContainerSpecialization
 SourcePropositionalRebase SourcePropositionalTemplates SourceSeparationSubset SourceWFSeparationWitness SourceWFSeparationConstructor SetSchemaConstructors SchemaConstructorBounds.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_subset_exists M phi o a N k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->
 exists out body,source_rec_exa_subset_chart M phi(succM M o)(succM M a)(succM M N)(zeroM M)body /\
 sf_relation M SFEx body(zeroM M)out /\source_zfr_provable M out.
Proof.
 intros BP BO BA BN.
 destruct(source_rec_exa_total M phi(zeroM M)(succM M o)(succM M a)(succM M N))as(theta&HT).
 destruct(source_rec_exa_total M phi(zeroM M)(succM M(succM M o))(succM M(succM M a))(succM M(succM M N)))as(p1&HP1).
 pose proof(source_rec_exa_bounded M phi(zeroM M)(succM M o)(succM M a)(succM M N)theta(succM M k)BP
  (coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)HT)as BT.
 pose proof(source_rec_exa_cutoff_one M phi o a N theta p1 BP HT HP1)as HC.
 destruct(source_zfr_separation_container_total M theta k p1 N BT HC)as(out&HO&PO).
 unfold E_separation_container,E_sf_ex,E_sf_all in HO.
 destruct(schema_expression_quantifier_split M _ SFEx _ out HO)as(body&HBody&HEx).
 destruct(schema_expression_quantifier_split M _ SFAll _ body HBody)as(point&HPoint&HAll).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M N)))as(mn&HMN).
 apply(proj1(source_sep_container_point_graph M N p1 mn point HMN))in HPoint.
 exists out,body. split;[exists point;split;[|exact HAll]|auto].
 exists(source_sep_left_code M),mn,p1. split;[exact(sf_make_numeral M SFMember 0 1)|].
 split;[exact HMN|]. split;[exact HP1|]. exact HPoint.
Qed.
Print Assumptions source_zfr_rec_exa_subset_exists.
