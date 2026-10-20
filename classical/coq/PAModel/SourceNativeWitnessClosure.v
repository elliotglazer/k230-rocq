(** Actual input-AllI closure of the native reflected requests. The fixed
 no-self axiom context produced inside the branch is pulled out using its
 proved closedness, rather than assuming a uniform branch-proof family. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceUpperWitnessRecipes SourceWitnessThetaRecipe SourceNativeWitnessRequestTotal
 SourceWitnessThetaInstances SourceNativeReflectionShift SourceWitnessPointMembers SourceNativeWitnessMatrixAlignment SourceNativeWitnessBounds
 SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks SourceMembershipBlockProofs
 SourceNativeRelativeWitness SourcePropositionalRebase SourceInternalLiftLaws SourceClosedZFRQuantifier
 SourceZFRProvability ContextCombination NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull
 SourceQuantifierRules SourceContextProofHelpers SourceProofRenaming.
Unset Implicit Arguments.
Theorem source_full_native_reflected_witness_closure M domain phi shifted theta n beta carrier s t
 refl level block sY tY st raw gb gc gn k:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi(succM M(succM M n))->
 source_cutoff_shift M 2 phi shifted->source_witness_theta_recipe M phi theta->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)carrier raw->
 context_bounded M gb gc gn k->coding_lt M beta k->coding_lt M carrier k->coding_lt M s k->coding_lt M t k->
 (forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 2))k)->
 source_ordinary_reflection M domain(source_succ_iter M 4 n)theta beta refl->source_LL_instance M beta carrier level->
 source_membership_block M(code_numeral M 2)carrier n block->
 sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->sf_relation M SFMember s t st->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->source_full_prv M gb gc gn block->
 source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->
 exists matrix reflectedAll nb nc nn ub uc un,
 code_relation M(SetSchemaConstructors.schema_env3 matrix carrier carrier)(E_upper_witness_closed(CEvar 0)(CEvar 1))raw /\
 source_bounded M matrix(succM M(succM M k)) /\source_native_reflected_witness_closed M domain carrier matrix reflectedAll /\
 source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un reflectedAll.
Proof.
 intros HD BP HCut HTheta(native&HNative&HRaw)BC HB HY HS HT HNames HR HL HBlock HSY HTY HST PR PL PBlock PSY PTY PST.
 pose proof(source_witness_theta_recipe_bound M phi theta n BP HTheta)as BTheta.
 destruct(context_shift_total M gb gc gn)as(sb&sc&HShift).
 pose proof(context_shift_preserves_bound M gb gc gn sb sc k HShift BC)as BS.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M carrier))as(guard&HGuard).
 assert(BGuard:source_bounded M guard(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)guard(succM M k)(or_introl eq_refl)HGuard)).
   exact(conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M carrier k)HY)). }
 destruct(environment_cons_total M sb sc gn guard)as(bb&bc&bn&HCons).
 pose proof(proj2(context_bounded_cons M sb sc gn guard bb bc bn(succM M k)HCons)(conj BGuard BS))as BB.
 pose proof(source_full_cons_head M sb sc gn guard bb bc bn(succM M k)HCons BGuard BB)as PGuard.
 destruct(source_full_ordinary_reflection_shift M domain(source_succ_iter M 4 n)theta beta carrier refl level gb gc gn sb sc
  HD BTheta HR HL HShift PR PL)as(reflS&levelS&HReflS&HLevelS&PReflS&PLevelS).
 pose proof(source_full_cons_weaken M sb sc gn guard bb bc bn(succM M k)reflS HCons BB PReflS)as PRefl.
 pose proof(source_full_cons_weaken M sb sc gn guard bb bc bn(succM M k)levelS HCons BB PLevelS)as PLevel.
 destruct(source_membership_block_total M(code_numeral M 3)(succM M carrier)n)as(blockS&HBlockS).
 pose proof(source_membership_block_shift M(code_numeral M 2)carrier n block blockS HBlock HBlockS)as HBlockShift.
 pose proof(source_full_prv_renaming M gb gc gn block(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc blockS PBlock HShift HBlockShift)as PBlockS.
 pose proof(source_full_cons_weaken M sb sc gn guard bb bc bn(succM M k)blockS HCons BB PBlockS)as PBlockB.
 destruct(sf_relation_total M SFMember(succM M s)(succM M carrier))as(sYS&HSYS).
 destruct(sf_relation_total M SFMember(succM M t)(succM M carrier))as(tYS&HTYS).
 destruct(sf_relation_total M SFMember(succM M s)(succM M t))as(stS&HSTS).
 pose proof(source_full_shifted_member M gb gc gn sb sc s carrier sY sYS HShift HSY HSYS PSY)as PSYS.
 pose proof(source_full_shifted_member M gb gc gn sb sc t carrier tY tYS HShift HTY HTYS PTY)as PTYS.
 pose proof(source_full_shifted_member M gb gc gn sb sc s t st stS HShift HST HSTS PST)as PSTS.
 pose proof(source_full_cons_weaken M sb sc gn guard bb bc bn(succM M k)sYS HCons BB PSYS)as PSYB.
 pose proof(source_full_cons_weaken M sb sc gn guard bb bc bn(succM M k)tYS HCons BB PTYS)as PTYB.
 pose proof(source_full_cons_weaken M sb sc gn guard bb bc bn(succM M k)stS HCons BB PSTS)as PSTB.
 assert(HNamesS:forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 3))(succM M k)).
 { intros j HJ. change(coding_lt M(addM M j(succM M(code_numeral M 2)))(succM M k)).
   rewrite internal_add_succ_right. exact(proj2(coding_lt_succ_cancel M _ _)(HNames j HJ)). }
 destruct(source_full_native_witness_request_total M domain phi theta n(succM M beta)(succM M carrier)
  (zeroM M)(succM M s)(succM M t)(code_numeral M 3)reflS levelS blockS guard sYS tYS stS bb bc bn(succM M k)
  HD BP HTheta BB(proj2(coding_lt_succ_cancel M beta k)HB)(proj2(coding_lt_succ_cancel M carrier k)HY)
  (coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M s k)HS)(proj2(coding_lt_succ_cancel M t k)HT)
  HNamesS HReflS HLevelS HBlockS HGuard HSYS HTYS HSTS PRefl PLevel PBlockB PGuard PSYB PTYB PSTB)
  as(mb&mc&matrix&request&nb&nc&nn&ub&uc&un&HMapM&HMatrix&HRequest&HNC&HU&PRequest).
 pose proof(source_native_witness_matrix_alignment M phi shifted native mb mc matrix(succM M(succM M n))
  BP HCut HNative HMapM HMatrix)as E. subst matrix.
 pose proof(source_native_witness_matrix_bound M phi n mb mc native k BP HMapM HMatrix HNames)as BNative.
 pose proof(source_reflected_request_bound M domain(succM M carrier)native request(succM M k)
  HD BNative(proj2(coding_lt_succ_cancel M carrier k)HY)HRequest)as BRequest.
 destruct(sf_relation_total M SFImpl guard request)as(point&HPoint).
 destruct(sf_relation_total M SFAll point(zeroM M))as(reflectedAll&HAll).
 pose proof(proj2(source_bounded_accept_binary M SFImpl guard request point(succM M k)
  (or_intror(or_intror eq_refl))HPoint)(conj BGuard BRequest))as BPoint.
 pose proof(proj2(source_bounded_accept_unary M SFAll point reflectedAll k(or_introl eq_refl)HAll)BPoint)as BAll.
 destruct(source_full_closed_zfr_guarded_all M gb gc gn sb sc guard bb bc bn nb nc nn ub uc un request point reflectedAll k
  BC BAll HShift HCons HNC HU HPoint HAll PRequest)as(vb&vc&vn&HV&PAll).
 exists native,reflectedAll,nb,nc,nn,vb,vc,vn. split;[exact HRaw|]. split;[exact BNative|]. split.
 - exists guard,request,point. repeat first[assumption|split].
 - repeat first[assumption|split].
Qed.
Print Assumptions source_full_native_reflected_witness_closure.
