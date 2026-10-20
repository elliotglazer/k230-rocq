(** Chosen reflected carrier data gives Separation's actual reflected branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalContextRenaming NumericalSourceFull SourceContextTransport SourceLFixed SourceD0Recipe
 SourceLSeparationCarrierShell SourceLDefinableProfile SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionShift
 SourceHierarchySyntax SourceHierarchyShifts SourceMembershipBlocks SourceMembershipBlockTail SourceLLevelDataShifts
 SourceRelativization SourceSetRelativization SourceLSeparationReflectionGraph SourceProofRenaming.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_full_L_separation_chosen_reflection M phi matrix params d refl level block lp sp allr
 gb gc gn ub uc tb tc k:
 source_bounded M phi(succM M params) ->source_bounded M matrix(succM M(succM M k)) ->
 context_bounded M gb gc gn k ->context_shift M gb gc gn ub uc ->context_shift M ub uc gn tb tc ->
 coding_lt M d k ->coding_lt M(code_numeral M 2)(succM M(succM M k)) ->
 (forall i,coding_lt M i(succM M params) ->coding_lt M(addM M i(code_numeral M 3))(succM M(succM M k))) ->
 source_cutoff_shift_thrice M phi matrix ->
 source_ordinary_reflection M(source_L_domain_code M)(succM M params)phi d refl ->
 source_LL_instance M d(zeroM M)level ->source_membership_block M(code_numeral M 1)(zeroM M)(succM M params)block ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 source_full_prv M gb gc gn refl ->source_full_prv M gb gc gn level ->source_full_prv M gb gc gn block ->
 source_full_prv M ub uc gn allr.
Proof.
 intros HP BM HC HS HT BD B2 HNames HMatrix HR HL HB HLP HSP HG PR PL PB.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(context_shift_preserves_bound M gb gc gn ub uc k HS HC)as HUC.
 pose proof(context_shift_preserves_bound M ub uc gn tb tc(succM M k)HT HUC)as HTC.
 destruct(source_ordinary_reflection_total M(source_L_domain_code M)(succM M params)phi(succM M d))as(r1&HR1).
 destruct(source_ordinary_reflection_total M(source_L_domain_code M)(succM M params)phi(succM M(succM M d)))as(r2&HR2).
 pose proof(source_full_ordinary_reflection_shift M(source_L_domain_code M)(succM M params)phi d refl r1
  gb gc gn ub uc HD HP HR HR1 HS PR)as PR1.
 pose proof(source_full_ordinary_reflection_shift M(source_L_domain_code M)(succM M params)phi(succM M d)r1 r2
  ub uc gn tb tc HD HP HR1 HR2 HT PR1)as PR2.
 destruct(source_LL_instance_total M(succM M d)(code_numeral M 1))as(l1&HL1).
 destruct(source_LL_instance_total M(succM M(succM M d))(code_numeral M 2))as(l2&HL2).
 pose proof(source_full_prv_renaming M gb gc gn level(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc l1 PL HS
  (source_LL_shift_to M d(zeroM M)level l1 HL HL1))as PL1.
 pose proof(source_full_prv_renaming M ub uc gn l1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)tb tc l2 PL1 HT
  (source_LL_shift_to M(succM M d)(code_numeral M 1)l1 l2 HL1 HL2))as PL2.
 destruct(source_membership_block_total M(code_numeral M 2)(code_numeral M 1)(succM M params))as(b1&HB1).
 destruct(source_membership_block_total M(code_numeral M 3)(code_numeral M 2)(succM M params))as(b2&HB2).
 pose proof(source_full_membership_block_shift M(code_numeral M 1)(zeroM M)(succM M params)block b1 gb gc gn ub uc HB HB1 HS PB)as PB1.
 pose proof(source_full_membership_block_shift M(code_numeral M 2)(code_numeral M 1)(succM M params)b1 b2 ub uc gn tb tc HB1 HB2 HT PB1)as PB2.
 destruct(source_membership_block_total M(code_numeral M 4)(code_numeral M 2)params)as(tail&HTail).
 destruct(sf_relation_total M SFMember(code_numeral M 3)(code_numeral M 2))as(head&HHead).
 destruct(source_full_membership_block_head_tail M(code_numeral M 3)(code_numeral M 2)params b2 tail head tb tc gn(succM M(succM M k))
  HNames B2 HB2 HTail HHead HTC PB2)as(_&PTail).
 apply(source_full_L_separation_carrier_reflection M phi matrix params(succM M(succM M d))r2 l2 tail lp sp allr
  ub uc gn tb tc(succM M k)HP BM HUC HT HTC).
 - apply(proj2(coding_lt_succ_cancel M(succM M d)(succM M k))),coding_lt_succ_cancel. exact BD.
 - exact B2.
 - intros i HI.
   assert(E:addM M i(code_numeral M 4)=succM M(succM M(succM M(succM M i)))).
   { rewrite Arithmetic.add_comm. change(addM M(succM M(succM M(succM M(succM M(zeroM M)))))i=succM M(succM M(succM M(succM M i)))).
     rewrite !Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. }
   rewrite <-E. change(coding_lt M(addM M i(succM M(code_numeral M 3)))(succM M(succM M k))).
   rewrite source_block_tail_index. apply HNames,coding_lt_succ_cancel. exact HI.
 - exact HMatrix.
 - exact HR2.
 - exact HL2.
 - exact HTail.
 - exact HLP.
 - exact HSP.
 - exact HG.
 - exact PR2.
 - exact PL2.
 - exact PTail.
Qed.
Print Assumptions source_full_L_separation_chosen_reflection.
