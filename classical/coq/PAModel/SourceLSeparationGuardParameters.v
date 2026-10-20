(** The real input-set guard and exact parameter domain table prove the complete L-parameter block. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded NumericalContexts NumericalEnvironments
 NumericalContextRenaming NumericalSourceFull SourceLFixed SourceRelativizationBounds SourceInternalLiftLaws SourceDomainContexts SourceDomainInstances SourcePredicateBlocks SourcePredicateBlockProofs
 SourceProofWeakening SourceContextTransport SourceTraceBounds SourceClosedContextShift ContextCombination SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_full_L_separation_guard_parameters M count ab ac an db dc b c n sb sc ub uc un block:
 source_zfr_context M ab ac an ->source_domain_context M(source_L_domain_code M)count db dc ->
 context_union M ab ac an db dc count b c n ->context_shift M b c n sb sc ->
 environment_cons M sb sc n(source_L_domain_code M)ub uc un ->
 source_predicate_block M(zeroM M)(source_L_domain_code M)(succM M count)block ->source_full_prv M ub uc un block.
Proof.
 intros HA HDomain HU HS HCons HB.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)count(source_zfr_context_closed M ab ac an HA)(coding_zero_lt_succ M count))as HAB.
 pose proof(source_domain_context_bounded M(source_L_domain_code M)count db dc HD HDomain)as HDB.
 pose proof(source_context_union_bounded M ab ac an db dc count b c n count HU HAB HDB)as HC.
 pose proof(context_shift_preserves_bound M b c n sb sc count HS HC)as HSC.
 pose proof(proj2(context_bounded_cons M sb sc n(source_L_domain_code M)ub uc un(succM M count)HCons)
  (conj(sr_domain_bound_succ M(source_L_domain_code M)count HD)HSC))as HBC.
 destruct(context_shift_total M db dc count)as(ds&dt&HDS).
 destruct(environment_cons_total M ds dt count(source_L_domain_code M))as(eb&ec&en&HECons).
 pose proof(proj1 HECons)as EL. subst en.
 pose proof(source_domain_context_cons_shift M(source_L_domain_code M)count db dc ds dt eb ec(succM M count)HD HDomain HDS HECons)as HEDomain.
 pose proof(context_union_right M ab ac an db dc count b c n HU)as HRight.
 pose proof(source_context_included_shift M db dc count b c n ds dt sb sc HRight HDS HS)as HShiftInclude.
 pose proof(source_context_included_cons M ds dt count sb sc n(source_L_domain_code M)eb ec(succM M count)ub uc un
  HShiftInclude HECons HCons)as HIncluded.
 apply(source_full_predicate_block_intro M(zeroM M)(source_L_domain_code M)(succM M count)block ub uc un(succM M count)).
 - intros i HI. now rewrite coding_add_zero_r.
 - exact HD.
 - exact HB.
 - exact HBC.
 - intros i f HI HF. apply full_source_Ctx.
   + exists(succM M count). split;[|exact HBC].
     apply(source_domain_instance_bound M(source_L_domain_code M)(addM M i(zeroM M))f(succM M count)HD);[now rewrite coding_add_zero_r|exact HF].
   + apply HIncluded. apply(proj2(source_domain_context_member_iff M(source_L_domain_code M)(succM M count)eb ec f HEDomain)).
     exists i. split;[exact HI|]. now rewrite coding_add_zero_r in HF.
Qed.
Print Assumptions source_full_L_separation_guard_parameters.
