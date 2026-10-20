(** The chosen reflected carrier supplies every Separation branch input except the actual local definability proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalContextRenaming NumericalSourceFull NumericalInstantiation NumericalRenaming SourceProofRenaming
 SourceLFixed SourceD0Recipe SourceLMatrixRecipes SourceLDefinableProfile SourceLSeparationCarrierShell
 SourceLSeparationHierarchyProof SourceLSeparationChosenReflection SourceRelativization SourceSetRelativization
 SourceOrdinaryReflectionSyntax SourceMembershipBlocks SourceMembershipBlockProofs SourceHierarchySyntax SourceHierarchyShifts
 SourceOrdinalPredicate SourceZFRProvability ContextCombination.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Lemma source_lsep_add_one M i:addM M i(code_numeral M 1)=succM M i.
Proof. rewrite Arithmetic.add_comm. change(addM M(succM M(zeroM M))i=succM M i). now rewrite Arithmetic.add_succ,Arithmetic.add_zero. Qed.
Lemma source_lsep_add_three M i:addM M i(code_numeral M 3)=succM M(succM M(succM M i)).
Proof. rewrite Arithmetic.add_comm. change(addM M(succM M(succM M(succM M(zeroM M))))i=succM M(succM M(succM M i))).
 rewrite !Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. Qed.
Theorem source_full_L_chosen_carrier_separation M phi psi matrix lp sp defex allr out params wide
 gb gc gn ub uc d ordinal level refl block:
 source_bounded M phi(succM M params) ->coding_lt M params(succM M wide) ->
 source_l_psiS M phi psi ->source_cutoff_shift_thrice M phi matrix ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 source_L_definable_profile M psi defex ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 code_relation M(L_definable_profile_environment lp(source_L_domain_code M))(E_L_carrier_separation(CEvar 1)(CEvar 0))out ->
 context_bounded M gb gc gn(succM M(succM M wide)) ->context_shift M gb gc gn ub uc ->
 coding_lt M d(succM M(succM M wide)) ->
 numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->source_LL_instance M d(zeroM M)level ->
 source_ordinary_reflection M(source_L_domain_code M)(succM M params)phi d refl ->
 source_membership_block M(code_numeral M 1)(zeroM M)(succM M params)block ->
 source_full_prv M gb gc gn defex ->source_full_prv M gb gc gn ordinal ->source_full_prv M gb gc gn level ->
 source_full_prv M gb gc gn refl ->source_full_prv M gb gc gn block ->
 exists ab ac an wb wc wn,source_zfr_context M ab ac an /\context_union M ab ac an gb gc gn wb wc wn /\
 source_full_prv M wb wc wn out.
Proof.
 intros HP HCount HPsi HMatrix HLP HSP HDef HRef HOut HC HS BD HO HL HR HB PDef PO PL PR PB.
 assert(HPWide:source_bounded M phi(succM M wide)).
 { exact(SourceBoundMonotone.source_bounded_monotone M phi(succM M params)(succM M wide)HP
   (proj2(coding_lt_succ_cancel M params(succM M wide))HCount)). }
 pose proof(source_cutoff_shift_thrice_bounded M phi matrix wide HPWide HMatrix)as BM.
 assert(HParam:forall i,coding_lt M i(succM M params) ->coding_lt M i(succM M wide)).
 { intros i HI. exact(source_bound_lt_le M i(succM M params)(succM M wide)HI
    (proj2(coding_lt_succ_cancel M params(succM M wide))HCount)). }
 assert(HNames:forall i,coding_lt M i(succM M params) ->coding_lt M(addM M i(code_numeral M 1))(succM M(succM M wide))).
 { intros i HI. rewrite source_lsep_add_one. apply coding_lt_succ_cancel,HParam. exact HI. }
 assert(HNamesFinal:forall i,coding_lt M i(succM M params) ->
  coding_lt M(addM M i(code_numeral M 3))(succM M(succM M(succM M(succM M wide))))).
 { intros i HI. rewrite source_lsep_add_three. apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel,HParam. exact HI. }
 assert(B2:coding_lt M(code_numeral M 2)(succM M(succM M(succM M(succM M wide))))).
 { change(coding_lt M(succM M(succM M(zeroM M)))(succM M(succM M(succM M(succM M wide))))).
   apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
 destruct(context_shift_total M ub uc gn)as(tb&tc&HT).
 pose proof(source_full_L_separation_chosen_reflection M phi matrix params d refl level block lp sp allr gb gc gn ub uc tb tc
  (succM M(succM M wide))HP BM HC HS HT BD B2 HNamesFinal HMatrix HR HL HB HLP HSP HRef PR PL PB)as PRef.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(succM M d))as(o1&HO1).
 destruct(source_LL_instance_total M(succM M d)(code_numeral M 1))as(l1&HL1).
 pose proof(source_full_prv_renaming M gb gc gn ordinal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc o1 PO HS
  (source_domain_shift_to M(source_ordinal_predicate_code M)d ordinal o1(source_ordinal_predicate_bounded M)HO HO1))as PO1.
 pose proof(source_full_prv_renaming M gb gc gn level(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc l1 PL HS
  (source_LL_shift_to M d(zeroM M)level l1 HL HL1))as PL1.
 destruct(sf_relation_total M SFMember(code_numeral M 1)(zeroM M))as(member&HM).
 assert(PM:source_full_prv M gb gc gn member).
 { apply(source_full_membership_block_project M(code_numeral M 1)(zeroM M)(succM M params)block gb gc gn
    (succM M(succM M wide))(zeroM M)member HNames(coding_zero_lt_succ M(succM M wide))HB HC PB(coding_zero_lt_succ M params)).
   now rewrite Arithmetic.add_zero. }
 destruct(sf_relation_total M SFMember(code_numeral M 2)(code_numeral M 1))as(m1&HM1).
 assert(RM:SourceQuantifierRules.source_formula_shift M member m1).
 { apply(proj2(numerical_renaming_member M(code_numeral M 1)(zeroM M)member(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)m1 HM)).
   exists(code_numeral M 2),(code_numeral M 1). split;[apply context_shift_lookup;reflexivity|].
   split;[apply context_shift_lookup;reflexivity|exact HM1]. }
 pose proof(source_full_prv_renaming M gb gc gn member(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc m1 PM HS RM)as PM1.
 destruct(code_relation_total M E_L_carrier_transitive(fun _=>zeroM M))as(allt&HTrans).
 exact(source_full_L_psiS_hierarchy_separation M phi psi matrix lp sp defex allr allt out wide gb gc gn ub uc(succM M d)o1 l1 m1
  HPWide HPsi HMatrix HLP HSP HDef HRef HTrans HOut HC HS HO1 HL1 HM1 PDef PRef PO1 PL1 PM1).
Qed.
Print Assumptions source_full_L_chosen_carrier_separation.
