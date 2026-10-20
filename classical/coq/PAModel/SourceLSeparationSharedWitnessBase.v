(** Eliminate the fresh reflected ordinal while retaining the original matrix parameters and source context. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SchemaRenamingDescriptors SchemaRenamingBounds NumericalContexts NumericalEnvironments NumericalSourceFull NumericalInstantiation
 SourceLFixed SourceLMatrixRecipes SourceD0Recipe SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceLDefinableProfile
 SourceLSeparationCarrierShell SourceLSeparationWitnessShift SourceLSeparationSharedCarrierBase SourceLSeparationCarrierElimination
 SourceCommonReflectedLevel SourceCommonReflectedOpening SourceFreshQuantifierProofs SourceZFRProvability ContextCombination
 SourceInternalLiftLaws SourceLeastOrdinalWitness SourceProofWeakening SourceContextTransport SourceContextProofHelpers SourceTraceBounds SourceClosedContextShift.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_L_separation_shared_witness_base M phi psi body matrix rp lp sp defex allr witness params:
 source_bounded M phi(succM M params) ->source_l_psiS M phi psi ->schema_renaming M SepBody phi body ->
 source_cutoff_shift_thrice M phi matrix ->source_relativization M(source_L_domain_code M)body rp ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 source_L_definable_profile M psi defex ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 code_relation M(L_definable_profile_environment rp(source_L_domain_code M))(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
 exists fb fc fn,source_zfr_context M fb fc fn /\
 forall b c n whole,
 context_included M fb fc fn b c n ->context_bounded M b c n(succM M params) ->
 source_common_reflected_level_recipe M(zeroM M)(succM M params)(succM M params)phi whole ->source_full_prv M b c n whole ->
 exists ab ac an ub uc un,source_zfr_context M ab ac an /\context_union M ab ac an b c n ub uc un /\source_full_prv M ub uc un witness.
Proof.
 intros HP HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness.
 destruct(source_L_separation_shared_carrier_base M phi psi body matrix rp lp sp defex allr witness params
  HP HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness)as(fb&fc&fn&HBase&PBase).
 exists fb,fc,fn. split;[exact HBase|]. intros b c n whole HIncluded HC HWhole PWhole.
 set(beta:=succM M params).
 destruct(source_common_reflected_level_point_total M(code_numeral M 1)(succM M params)(succM M params)phi(succM M beta)(zeroM M))as(point&HPoint).
 destruct(sf_relation_total M SFEx point(zeroM M))as(opened&HOpened).
 destruct(source_common_reflected_beta_opening M(zeroM M)(succM M params)(succM M params)phi beta whole point opened HP HWhole HPoint HOpened)
 as(rawbody&HRawEx&HOpen).
 assert(BWhole:source_bounded M whole(succM M params)).
 { apply(source_common_reflected_level_recipe_bounded M(zeroM M)(succM M params)(succM M params)phi whole(succM M params)HP);[|exact HWhole].
   intros i HI. now rewrite coding_add_zero_r. }
 pose proof(proj1(source_bounded_accept_unary M SFEx rawbody whole(succM M params)(or_intror eq_refl)HRawEx)BWhole)as BRaw.
 assert(BRawWide:source_bounded M rawbody(succM M(succM M(succM M params)))).
 { apply(SourceBoundMonotone.source_bounded_monotone M rawbody(succM M(succM M params))(succM M(succM M(succM M params)))BRaw).
   apply(proj2(coding_lt_succ_cases M _ _)). left. apply coding_lt_succ. }
 assert(BOpened:source_bounded M opened(succM M(succM M params))).
 { exact(numerical_instantiation_bounded M rawbody beta opened(succM M(succM M params))BRawWide(coding_lt_succ M beta)HOpen). }
 assert(HCW:context_bounded M b c n(succM M(succM M params))).
 { apply(context_bounded_monotone M b c n(succM M params)(succM M(succM M params))HC).
   apply(proj2(coding_lt_succ_cases M _ _)). left. apply coding_lt_succ. }
 destruct(environment_cons_total M b c n opened)as(b1&c1&n1&HCons).
 pose proof(proj2(context_bounded_cons M b c n opened b1 c1 n1(succM M(succM M params))HCons)(conj BOpened HCW))as HB1.
 pose proof(source_full_cons_head M b c n opened b1 c1 n1(succM M(succM M params))HCons BOpened HB1)as POpened.
 assert(HBaseBranch:context_included M fb fc fn b1 c1 n1).
 { intros f HF. exact(source_cons_tail_inclusion M b c n opened b1 c1 n1 HCons f(HIncluded f HF)). }
 assert(HCount:coding_lt M params(succM M(succM M params))).
 { exact(coding_lt_trans M params(succM M params)(succM M(succM M params))(coding_lt_succ M params)(coding_lt_succ M(succM M params))). }
 destruct(PBase(succM M params)b1 c1 n1 beta point opened HBaseBranch HCount HB1(coding_lt_succ M beta)HPoint HOpened POpened)
 as(ab&ac&an&wb&wc&wn&HAC&HBranchUnion&PWitness).
 destruct(context_union_total M ab ac an b c n)as(ub&uc&un&HUnion).
 pose proof(context_union_left M ab ac an b c n ub uc un HUnion)as HLeft.
 pose proof(context_union_right M ab ac an b c n ub uc un HUnion)as HRight.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)(succM M params)(source_zfr_context_closed M ab ac an HAC)
  (coding_zero_lt_succ M(succM M params)))as HAB.
 pose proof(source_context_union_bounded M ab ac an b c n ub uc un(succM M params)HUnion HAB HC)as HUC.
 assert(HUCW:context_bounded M ub uc un(succM M(succM M params))).
 { apply(context_bounded_monotone M ub uc un(succM M params)(succM M(succM M params))HUC).
   apply(proj2(coding_lt_succ_cases M _ _)). left. apply coding_lt_succ. }
 destruct(environment_cons_total M ub uc un opened)as(db&dc&dn&HNewCons).
 pose proof(proj2(context_bounded_cons M ub uc un opened db dc dn(succM M(succM M params))HNewCons)(conj BOpened HUCW))as HNewBound.
 assert(HTransfer:context_included M wb wc wn db dc dn).
 { intros f HF. apply(proj1(proj2 HBranchUnion f))in HF.
   apply(proj2(context_member_cons M ub uc un opened db dc dn f HNewCons)).
   destruct HF as[HF|HF].
   - right. exact(HLeft f HF).
   - apply(proj1(context_member_cons M b c n opened b1 c1 n1 f HCons))in HF.
     destruct HF as[E|HF];[now left|right;exact(HRight f HF)]. }
 pose proof(source_full_prv_weaken_bounded M wb wc wn db dc dn witness(succM M(succM M params))PWitness HTransfer HNewBound)as PWitnessNew.
 pose proof(source_relativization_preserves_bound M body(source_L_domain_code M)(succM M(succM M(succM M params)))rp
  (numerical_L_domain_bounded M)(schema_separation_bound M phi body params HP HBody)HRP)as BRP.
 pose proof(source_lsep_canonical_witness_bounded M(source_L_domain_code M)rp witness params(numerical_L_domain_bounded M)BRP HWitness)as BWitness.
 assert(BWitnessW:source_bounded M witness(succM M(succM M params))).
 { apply(SourceBoundMonotone.source_bounded_monotone M witness(succM M params)(succM M(succM M params))BWitness).
   apply(proj2(coding_lt_succ_cases M _ _)). left. apply coding_lt_succ. }
 destruct(sf_relation_total M SFImpl opened witness)as(imp&HImp).
 assert(PImp:source_full_prv M ub uc un imp).
 { apply(full_source_II M ub uc un opened witness imp db dc dn).
   - exists(succM M(succM M params)). split;[|exact HUCW].
     exact(proj2(source_bounded_accept_binary M SFImpl opened witness imp(succM M(succM M params))(or_intror(or_intror eq_refl))HImp)(conj BOpened BWitnessW)).
   - exact PWitnessNew.
   - exact HNewCons.
   - exact HImp. }
 exists ab,ac,an,ub,uc,un. split;[exact HAC|]. split;[exact HUnion|].
 exact(source_full_fresh_exists_elim M ub uc un rawbody whole beta opened witness imp(succM M params)HUC BRaw BWitness
  (coding_lt_succ M beta)HRawEx HOpen HImp PImp
  (source_full_prv_weaken_bounded M b c n ub uc un whole(succM M params)PWhole HRight HUC)).
Qed.
Print Assumptions source_L_separation_shared_witness_base.
