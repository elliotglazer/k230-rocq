(** The actual native carrier rule needs domain proofs only for original
 parameters and its selected carrier. No domain assumption names an ordinal,
 cofinal K witness, or auxiliary proof variable. Thus later fresh ExE is valid. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceFiniteCutoffShift SourceNativeKRecipes SourceUpperTraceProfile SourceUpperTraceFrame SourceUpperWitnessRecipes
 SourceZeroTransposition SourceNativeCarrierLaw SourceUpperPremiseBounds SourcePureRelativeSupportedRule
 SourceNativeSupportProjection SourceNativeCarrierProjection SourceFiniteTelescope SourceRelativization
 NumericalRenaming NumericalContexts NumericalInstantiation NumericalSourceFull SourceDerivedRules SourceContextTransport.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_full_native_relative_carrier_supported M domain phi shifted n fresh tb tc
 profile exprofile witness subsetclosed xb pb target relative ie iw iset ix ip re rw rs b c l:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi(succM M(succM M n))->
 source_cutoff_shift M 2 phi shifted->coding_lt M(succM M(succM M n))fresh->source_zero_transposition M fresh tb tc->
 source_upper_trace_profile M shifted profile->sf_relation M SFEx profile(zeroM M)exprofile->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)(zeroM M)witness->source_subset_closed_graph M(zeroM M)subsetclosed->
 sf_relation M SFMember fresh(zeroM M)xb->sf_relation M SFMember(code_numeral M 1)(zeroM M)pb->
 source_upper_conclusion_recipe M phi target->source_relativization M domain target relative->
 numerical_renaming M exprofile tb tc(succM M fresh)(zeroM M)ie->
 numerical_renaming M witness tb tc(succM M fresh)(zeroM M)iw->
 numerical_renaming M subsetclosed tb tc(succM M fresh)(zeroM M)iset->
 sf_relation M SFMember(zeroM M)fresh ix->sf_relation M SFMember(code_numeral M 1)fresh ip->
 source_relativization M domain ie re->source_relativization M domain iw rw->source_relativization M domain iset rs->
 source_context_finite_bound M b c l->
 (forall i di,coding_lt M i(succM M(succM M n))->numerical_instantiation M domain i di->source_full_prv M b c l di)->
 (forall di,numerical_instantiation M domain fresh di->source_full_prv M b c l di)->
 source_full_prv M b c l re->source_full_prv M b c l rw->source_full_prv M b c l rs->
 source_full_prv M b c l ix->source_full_prv M b c l ip->source_full_prv M b c l relative.
Proof.
 intros HD BP HCut HF HTrans HProfile HEx HW HS HXB HPB HT HR RE RW RS HIX HIP HRE HRW HRS HC PD PY PE PW PS PX PP.
 assert(B1:coding_lt M(code_numeral M 1)(succM M(succM M n))).
 { apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M n))). apply coding_zero_lt_succ. }
 assert(H1Z:code_numeral M 1<>zeroM M).
 { intro E. pose proof(coding_zero_lt_succ M(zeroM M))as H. change(coding_lt M(zeroM M)(code_numeral M 1))in H.
   rewrite E in H. exact(coding_not_lt_zero M _ H). }
 assert(H1F:code_numeral M 1<>fresh).
 { intro E. pose proof(coding_lt_trans M(code_numeral M 1)(succM M(succM M n))fresh B1 HF)as H.
   rewrite <-E in H. apply(proj1(coding_lt_succ_cancel M(zeroM M)(zeroM M)))in H. exact(coding_not_lt_zero M _ H). }
 assert(RX:numerical_renaming M xb tb tc(succM M fresh)(zeroM M)ix).
 { apply(proj2(numerical_renaming_member M fresh(zeroM M)xb tb tc(succM M fresh)(zeroM M)ix HXB)).
   exists(zeroM M),fresh. split;[exact(source_zero_transposition_name M fresh tb tc HTrans)|].
   split;[exact(source_zero_transposition_zero M fresh tb tc HTrans)|exact HIX]. }
 assert(RP:numerical_renaming M pb tb tc(succM M fresh)(zeroM M)ip).
 { apply(proj2(numerical_renaming_member M(code_numeral M 1)(zeroM M)pb tb tc(succM M fresh)(zeroM M)ip HPB)).
   exists(code_numeral M 1),fresh. split;[exact(source_zero_transposition_other M fresh tb tc(code_numeral M 1)HTrans H1Z H1F)|].
   split;[exact(source_zero_transposition_zero M fresh tb tc HTrans)|exact HIP]. }
 destruct(sf_relation_total M SFImpl ip target)as(l5&H5).
 destruct(sf_relation_total M SFImpl ix l5)as(l4&H4).
 destruct(sf_relation_total M SFImpl iset l4)as(l3&H3).
 destruct(sf_relation_total M SFImpl iw l3)as(l2&H2).
 destruct(sf_relation_total M SFImpl ie l2)as(law&H1).
 assert(HLaw:source_native_carrier_law_graph M fresh tb tc exprofile witness subsetclosed xb pb target law).
 { exists ie,iw,iset,ix,ip,l5,l4,l3,l2. repeat first[assumption|split]. }
 pose proof(source_full_native_carrier_law M phi shifted n fresh tb tc profile exprofile witness subsetclosed xb pb target law
  BP HCut HF HTrans HProfile HEx HW HS HXB HPB HT HLaw)as PLaw.
 assert(TLaw:source_finite_telescope M[ie;iw;iset;ix;ip]target law).
 { exists l2. split;[|exact H1]. exists l3. split;[|exact H2]. exists l4. split;[|exact H3].
   exists l5. split;[|exact H4]. exists target. split;[reflexivity|exact H5]. }
 pose proof(source_cutoff_shift_bounded M 2 phi shifted n BP HCut)as BShift.
 pose proof(source_upper_trace_profile_bound M shifted profile(succM M n)BShift HProfile)as BProfile.
 pose proof(proj2(source_bounded_accept_unary M SFEx profile exprofile(succM M(succM M n))(or_intror eq_refl)HEx)BProfile)as BE.
 pose proof(source_upper_witness_carrier_bound M shifted witness(succM M n)BShift HW)as BW.
 assert(BS:source_bounded M subsetclosed(succM M(succM M n))).
 { apply(source_bounded_monotone M subsetclosed(code_numeral M 1)(succM M(succM M n))(source_subset_carrier_bound M subsetclosed HS)).
   exact(coding_lt_trans M(code_numeral M 1)(succM M(succM M n))(succM M(succM M(succM M n)))B1(coding_lt_succ M _)). }
 pose proof(source_upper_conclusion_recipe_bound M phi target n BP HT)as BT.
 destruct(sf_relation_total M SFImpl ip relative)as(r5&G5).
 destruct(sf_relation_total M SFImpl ix r5)as(r4&G4).
 destruct(sf_relation_total M SFImpl rs r4)as(r3&G3).
 destruct(sf_relation_total M SFImpl rw r3)as(r2&G2).
 destruct(sf_relation_total M SFImpl re r2)as(rlaw&G1).
 pose proof(source_relativization_atom M domain SFMember(zeroM M)fresh ix(or_introl eq_refl)HIX)as HRX.
 pose proof(source_relativization_atom M domain SFMember(code_numeral M 1)fresh ip(or_introl eq_refl)HIP)as HRP.
 assert(HR5:source_relativization M domain l5 r5).
 { exact(source_relativization_binary M domain SFImpl ip target l5 ip relative r5(or_intror(or_intror eq_refl))H5 HRP HR G5). }
 assert(HR4:source_relativization M domain l4 r4).
 { exact(source_relativization_binary M domain SFImpl ix l5 l4 ix r5 r4(or_intror(or_intror eq_refl))H4 HRX HR5 G4). }
 assert(HR3:source_relativization M domain l3 r3).
 { exact(source_relativization_binary M domain SFImpl iset l4 l3 rs r4 r3(or_intror(or_intror eq_refl))H3 HRS HR4 G3). }
 assert(HR2:source_relativization M domain l2 r2).
 { exact(source_relativization_binary M domain SFImpl iw l3 l2 rw r3 r2(or_intror(or_intror eq_refl))H2 HRW HR3 G2). }
 assert(HR1:source_relativization M domain law rlaw).
 { exact(source_relativization_binary M domain SFImpl ie l2 law re r2 rlaw(or_intror(or_intror eq_refl))H1 HRE HR2 G1). }
 destruct(source_pure_relative_supported_rule M domain law HD PLaw)as(bound&HApply).
 destruct(source_native_support_projection_total M(succM M(succM M n))fresh bound)as(rb&rc&HProjection).
 pose proof(source_native_five_premise_projection_fixed M(succM M(succM M n))fresh tb tc
  exprofile witness subsetclosed ie iw iset ix ip target law bound rb rc BE BW BS BT B1 HF HTrans RE RW RS HIX HIP TLaw HProjection)as RLaw.
 assert(PRLaw:source_full_prv M b c l rlaw).
 { apply(HApply rb rc bound(zeroM M)law rlaw b c l RLaw HR1 HC).
   intros i j di HI Hij HDI. destruct(proj2(proj2 HProjection)i j HI Hij)as[HJ|[EJ|EJ]].
   - exact(PD j di HJ HDI).
   - subst j. exact(PY di HDI).
   - subst j. exact(PD(zeroM M)di(coding_zero_lt_succ M(succM M n))HDI). }
 pose proof(source_full_modus_ponens M b c l re r2 rlaw G1 PRLaw PE)as P2.
 pose proof(source_full_modus_ponens M b c l rw r3 r2 G2 P2 PW)as P3.
 pose proof(source_full_modus_ponens M b c l rs r4 r3 G3 P3 PS)as P4.
 pose proof(source_full_modus_ponens M b c l ix r5 r4 G4 P4 PX)as P5.
 exact(source_full_modus_ponens M b c l ip relative r5 G5 P5 PP).
Qed.
Print Assumptions source_full_native_relative_carrier_supported.
