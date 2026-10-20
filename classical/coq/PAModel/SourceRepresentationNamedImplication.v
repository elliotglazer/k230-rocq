(** Actual implication witness assembly in the fixed named frame.
    Every closure witness premise is an actual source proof and is consumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNumeralLift FixedSourceBounds SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorNamedPrograms
 SourceImplicationWitnessShell SourceNamedImplicationCertificates SourceAtomicNamedWitnesses SourceNamedClosureExistence
 SourceNamedQuantifierRules SourceNamedVacuity SourceNamedElimination SourceNamedVacuityImages SourceNamedFiniteCalibration
 SourceNamedDifferenceCertificates SourceNamedDifferenceFacts SourceDifferenceNumeralParameters SourceDifferenceProfile
 SourceRepresentationNamedWitness SourceRepresentationConjunctionFrame SourceRepresentationNamedConjunction SourceRepresentativeRenaming
 SourceZFRProvability SourceSetTheoryDescriptors.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope minZFsyn.
Unset Implicit Arguments.
Local Opaque code_numeral.
Definition IWN_operation2 M:=code_numeral M(sf_encode(source_difference_operation $6 $5 $0)).
Definition IWN_final_exists M:=code_numeral M(sf_encode(named_difference_exists 6 5 0)).
Definition IWN_environment M namedL namedR namedA result exTarget exL exR exA i:=match i with
 |0=>code_numeral M(sf_encode named_difference_successor)|1=>code_numeral M(sf_encode named_difference_closure)
 |2=>RNC_member M 3|3=>RNC_member M 4|4=>RNC_member M 5|5=>RNC_member M 0
 |6=>namedL|7=>namedR|8=>result|9=>RNC_operation1 M|10=>IWN_operation2 M
 |11=>RNC_middle_exists M|12=>IWN_final_exists M|13=>exTarget|14=>exL|15=>exR
 |16=>RNC_member M 6|17=>namedA|18=>exA|_=>zeroM M end.
Theorem source_zfr_named_implication_from_point M repL repR carrier namedL namedR namedA result condition inner body all law ml mr ma el er ea outL outR outA:
 source_bounded M repL(code_numeral M 2)->source_bounded M repR(code_numeral M 2)->
 source_bounded M carrier(code_numeral M 2)->source_bounded M result(code_numeral M 2)->
 source_representative_renaming M(code_numeral M 3)repL namedL->source_representative_renaming M(code_numeral M 4)repR namedR->source_representative_renaming M(code_numeral M 6)carrier namedA->
 sf_relation M SFAnd(RNC_operation1 M)(IWN_operation2 M)condition->sf_relation M SFImpl namedR result inner->
 sf_relation M SFImpl namedL inner body->sf_relation M SFImpl namedA body all->sf_relation M SFImpl condition all law->source_zfr_provable M law->
 sf_relation M SFAnd(RNC_member M 3)namedL ml->sf_relation M SFAnd(RNC_member M 4)namedR mr->sf_relation M SFAnd(RNC_member M 6)namedA ma->
 source_named_quantifier M false(code_numeral M 3)ml el->source_named_quantifier M false(code_numeral M 4)mr er->source_named_quantifier M false(code_numeral M 6)ma ea->
 code_relation M(named_closure_values M el)(source_prop_expression NCE_template)outL->source_zfr_provable M outL->
 code_relation M(named_closure_values M er)(source_prop_expression NCE_template)outR->source_zfr_provable M outR->
 code_relation M(named_closure_values M ea)(source_prop_expression NCE_template)outA->source_zfr_provable M outA->
 exists mt et out,sf_relation M SFAnd(RNC_member M 0)result mt/\source_named_quantifier M false(zeroM M)mt et/\
 code_relation M(named_closure_values M et)(source_prop_expression NCE_template)out/\source_zfr_provable M out.
Proof.
 intros BL BR BA BQ HNL HNR HNA HC HI HB HA HL PLaw HML HMR HMA HEL HER HEA GL PL GR PR GA PA.
 destruct(sf_relation_total M SFAnd(RNC_member M 0)result)as(mt&HMT).
 destruct(source_named_quantifier_total M false(zeroM M)mt)as(et&HET).
 set(rho:=IWN_environment M namedL namedR namedA result et el er ea).
 assert(GL0:code_relation M rho(source_prop_expression IRS_left)ml)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 2)(SPTSlot 6)(rho 2)(rho 6)ml eq_refl eq_refl HML)).
 assert(GR0:code_relation M rho(source_prop_expression IRS_right)mr)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 3)(SPTSlot 7)(rho 3)(rho 7)mr eq_refl eq_refl HMR)).
 assert(GA0:code_relation M rho(source_prop_expression IRS_An)ma)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 16)(SPTSlot 17)(rho 16)(rho 17)ma eq_refl eq_refl HMA)).
 assert(GT:code_relation M rho(source_prop_expression IRS_target)mt)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 5)(SPTSlot 8)(rho 5)(rho 8)mt eq_refl eq_refl HMT)).
 set(mm:=code_numeral M(sf_encode(named_difference_matrix 3 4 5))).
 set(mf:=code_numeral M(sf_encode(named_difference_matrix 6 5 0))).
 assert(GM:code_relation M rho(source_prop_expression IRS_middle)mm).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 4)(SPTSlot 9)(rho 4)(rho 9)mm eq_refl eq_refl
   (sf_make_numeral M SFAnd(sf_make SFMember 5 2)(sf_encode(source_difference_operation $3 $4 $5)))). }
 assert(GF:code_relation M rho(source_prop_expression IRS_final)mf).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 5)(SPTSlot 10)(rho 5)(rho 10)mf eq_refl eq_refl
   (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode(source_difference_operation $6 $5 $0)))). }
 pose proof(source_representation_witness_body_bound M result mt BQ HMT)as BMT.
 pose proof(source_named_quantifier_bound M false(zeroM M)mt et(code_numeral M 3)BMT HET)as BET.
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)repR)as(origR&HOrigR).
 pose proof(source_representation_named_witness_bound M(code_numeral M 4)repR namedR(RNC_member M 4)origR mr er BR
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)HNR(sf_make_numeral M SFMember 4 2)HOrigR HMR HER)as BER3.
 pose proof(RNC_representative_bound M repL namedL 3 BL ltac:(lia)HNL)as BNL.
 pose proof(RNC_representative_bound M repR namedR 4 BR ltac:(lia)HNR)as BNR.
 pose proof(RNC_representative_bound M carrier namedA 6 BA ltac:(lia)HNA)as BNA.
 assert(BOp1:source_bounded M(RNC_operation1 M)(code_numeral M 8)).
 { exact(difference_operation_parameters_bound M(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(code_numeral M 8)(RNC_operation1 M)
   (proj2(fixed_source_numeral_lt_iff M 3 8)ltac:(lia))(proj2(fixed_source_numeral_lt_iff M 4 8)ltac:(lia))(proj2(fixed_source_numeral_lt_iff M 5 8)ltac:(lia))(source_difference_operation_numeral_graph M 3 4 5)). }
 assert(BOp2:source_bounded M(IWN_operation2 M)(code_numeral M 8)).
 { exact(difference_operation_parameters_bound M(code_numeral M 6)(code_numeral M 5)(zeroM M)(code_numeral M 8)(IWN_operation2 M)
   (proj2(fixed_source_numeral_lt_iff M 6 8)ltac:(lia))(proj2(fixed_source_numeral_lt_iff M 5 8)ltac:(lia))(coding_zero_lt_succ M(code_numeral M 7))(source_difference_operation_numeral_graph M 6 5 0)). }
 assert(BMM:source_bounded M mm(code_numeral M 8)).
 { exact(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 5)(RNC_operation1 M)mm(code_numeral M 8)(or_introl eq_refl)
    (sf_make_numeral M SFAnd(sf_make SFMember 5 2)(sf_encode(source_difference_operation $3 $4 $5))))(conj(RNC_member_bound M 5 ltac:(lia))BOp1)). }
 assert(BMF:source_bounded M mf(code_numeral M 8)).
 { exact(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 0)(IWN_operation2 M)mf(code_numeral M 8)(or_introl eq_refl)
    (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode(source_difference_operation $6 $5 $0))))(conj(RNC_member_bound M 0 ltac:(lia))BOp2)). }
 pose proof(source_named_quantifier_bound M false(code_numeral M 5)mm(RNC_middle_exists M)(code_numeral M 8)BMM(named_difference_first_quantifier M))as BEM.
 pose proof(source_named_quantifier_bound M false(zeroM M)mf(IWN_final_exists M)(code_numeral M 8)BMF(named_implication_second_quantifier M))as BEF.
 assert(BEL:source_bounded M el(code_numeral M 8)).
 { exact(source_named_quantifier_bound M false(code_numeral M 3)ml el(code_numeral M 8)
   (proj2(source_bounded_accept_binary M SFAnd _ _ _ _ (or_introl eq_refl)HML)(conj(RNC_member_bound M 3 ltac:(lia))BNL))HEL). }
 assert(BEA:source_bounded M ea(code_numeral M 8)).
 { exact(source_named_quantifier_bound M false(code_numeral M 6)ma ea(code_numeral M 8)
   (proj2(source_bounded_accept_binary M SFAnd _ _ _ _ (or_introl eq_refl)HMA)(conj(RNC_member_bound M 6 ltac:(lia))BNA))HEA). }
 assert(BAll:forall idx,source_bounded M(rho idx)(code_numeral M 8)).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|idx]]]]]]]]]]]]]]]]]]];cbn[rho IWN_environment].
   - exact(proj1(named_difference_fixed_bounds M)).
   - exact(proj2(named_difference_fixed_bounds M)).
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - exact BNL.
   - exact BNR.
   - exact(source_bounded_monotone M _ _ _ BQ(proj2(fixed_source_numeral_lt_iff M 2 9)ltac:(lia))).
   - exact BOp1.
   - exact BOp2.
   - exact BEM.
   - exact BEF.
   - exact(source_bounded_monotone M _ _ _ BET(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact BEL.
   - exact(source_bounded_monotone M _ _ _ BER3(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - apply RNC_member_bound;lia.
   - exact BNA.
   - exact BEA.
   - apply source_bounded_accept_falsity. }
 assert(V0:source_prop_named_vacuity M rho(zeroM M)IRS_goal0).
 { cbn[source_prop_named_vacuity IRS_goal0 IRS_middle IRS_left IRS_right IRS_An rho IWN_environment]. repeat split.
   - exact(named_difference_member_vacuous M 0 5 ltac:(lia)ltac:(lia)).
   - exact(source_finite_named_vacuity M 0(source_difference_operation $3 $4 $5)eq_refl).
   - exact(named_difference_member_vacuous M 0 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repL namedL(code_numeral M 3)(zeroM M)BL HNL(source_fixed_numeral_neq M 3 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(named_difference_member_vacuous M 0 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repR namedR(code_numeral M 4)(zeroM M)BR HNR(source_fixed_numeral_neq M 4 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(named_difference_member_vacuous M 0 6 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M carrier namedA(code_numeral M 6)(zeroM M)BA HNA(source_fixed_numeral_neq M 6 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(source_named_quantifier_is_vacuous M false(zeroM M)mt et(code_numeral M 3)BMT HET). }
 assert(V5:source_prop_named_vacuity M rho(code_numeral M 5)IRS_goal5).
 { cbn[source_prop_named_vacuity IRS_goal5 IRS_left IRS_right IRS_An rho IWN_environment]. repeat split.
   - exact(named_difference_member_vacuous M 5 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repL namedL(code_numeral M 3)(code_numeral M 5)BL HNL(source_fixed_numeral_neq M 3 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(named_difference_member_vacuous M 5 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repR namedR(code_numeral M 4)(code_numeral M 5)BR HNR(source_fixed_numeral_neq M 4 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(named_difference_member_vacuous M 5 6 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M carrier namedA(code_numeral M 6)(code_numeral M 5)BA HNA(source_fixed_numeral_neq M 6 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 5 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 5 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 5)(code_numeral M 3)BET(proj2(fixed_source_numeral_lt_iff M 3 6)ltac:(lia))). }
 assert(V4:source_prop_named_vacuity M rho(code_numeral M 4)IRS_goal4).
 { cbn[source_prop_named_vacuity IRS_goal4 IRS_left IRS_An rho IWN_environment]. repeat split.
   - exact(named_difference_member_vacuous M 4 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repL namedL(code_numeral M 3)(code_numeral M 4)BL HNL(source_fixed_numeral_neq M 3 4 ltac:(lia))(source_fixed_numeral_neq M 1 4 ltac:(lia))).
   - exact(named_difference_member_vacuous M 4 6 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M carrier namedA(code_numeral M 6)(code_numeral M 4)BA HNA(source_fixed_numeral_neq M 6 4 ltac:(lia))(source_fixed_numeral_neq M 1 4 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 4)(code_numeral M 3)BET(proj2(fixed_source_numeral_lt_iff M 3 5)ltac:(lia))). }
 assert(V3:source_prop_named_vacuity M rho(code_numeral M 3)IRS_goal3).
 { cbn[source_prop_named_vacuity IRS_goal3 IRS_An rho IWN_environment]. repeat split.
   - exact(source_named_vacuous_above_bound M er(code_numeral M 3)(code_numeral M 3)BER3(coding_lt_succ M(code_numeral M 3))).
   - exact(named_difference_member_vacuous M 3 6 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M carrier namedA(code_numeral M 6)(code_numeral M 3)BA HNA(source_fixed_numeral_neq M 6 3 ltac:(lia))(source_fixed_numeral_neq M 1 3 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 3)(code_numeral M 3)BET(coding_lt_succ M(code_numeral M 3))). }
 assert(V6:source_prop_named_vacuity M rho(code_numeral M 6)IRS_goal6).
 { cbn[source_prop_named_vacuity IRS_goal6 rho IWN_environment]. repeat split.
   - apply source_finite_named_vacuity. reflexivity.
   - apply source_finite_named_vacuity. reflexivity.
   - exact(source_named_vacuous_above_bound M et(code_numeral M 6)(code_numeral M 3)BET(proj2(fixed_source_numeral_lt_iff M 3 7)ltac:(lia))). }
 assert(PPoint:source_descriptor_template M ZFRSourceDescriptor rho IRS_point).
 { intros f HF. assert(G:code_relation M rho(source_prop_expression IRS_point)law).
   { apply(source_prop_template_join M rho SFImpl(SPTAnd(SPTSlot 9)(SPTSlot 10))(SPTImpl(SPTSlot 17)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8))))condition all law);[| |exact HL].
     - exact(source_prop_template_join M rho SFAnd(SPTSlot 9)(SPTSlot 10)(RNC_operation1 M)(IWN_operation2 M)condition eq_refl eq_refl HC).
     - apply(source_prop_template_join M rho SFImpl(SPTSlot 17)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8)))namedA body all eq_refl);[|exact HA].
       apply(source_prop_template_join M rho SFImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8))namedL inner body eq_refl);[|exact HB].
       exact(source_prop_template_join M rho SFImpl(SPTSlot 7)(SPTSlot 8)namedR result inner eq_refl eq_refl HI). }
   rewrite(code_relation_functional M _ rho f law HF G). exact(proj2(source_zfr_descriptor_provable M law)PLaw). }
 assert(PFirst:source_descriptor_template M ZFRSourceDescriptor rho IRS_first).
 { intros f HF. assert(G:code_relation M rho(source_prop_expression IRS_first)(code_numeral M(sf_encode
   (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→named_difference_exists 3 4 5)))).
   { unfold IRS_first. repeat apply RNC_fixed_imp_graph;reflexivity. }
   rewrite(code_relation_functional M _ rho f _ HF G). exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_difference_first M)). }
 assert(PSecond:source_descriptor_template M ZFRSourceDescriptor rho IRS_second).
 { intros f HF. assert(G:code_relation M rho(source_prop_expression IRS_second)(code_numeral M(sf_encode
   (named_difference_successor →named_difference_closure →($6 ∈' $2)→($5 ∈' $2)→named_difference_exists 6 5 0)))).
   { unfold IRS_second. repeat apply RNC_fixed_imp_graph;reflexivity. }
   rewrite(code_relation_functional M _ rho f _ HF G). exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_implication_second M)). }
 pose proof(AWN_closure_template M ZFRSourceDescriptor rho 14 el outL eq_refl eq_refl eq_refl GL(proj2(source_zfr_descriptor_provable M outL)PL))as PTL.
 pose proof(AWN_closure_template M ZFRSourceDescriptor rho 15 er outR eq_refl eq_refl eq_refl GR(proj2(source_zfr_descriptor_provable M outR)PR))as PTR.
 pose proof(AWN_closure_template M ZFRSourceDescriptor rho 18 ea outA eq_refl eq_refl eq_refl GA(proj2(source_zfr_descriptor_provable M outA)PA))as PTA.
 pose proof(source_descriptor_implication_witness_shell M ZFRSourceDescriptor rho(code_numeral M 8)
  (zeroM M)(code_numeral M 5)(code_numeral M 4)(code_numeral M 3)(code_numeral M 6)mf mm ml mr ma mt
  BAll GF GM GL0 GR0 GA0 GT(named_implication_second_quantifier M)(named_difference_first_quantifier M)HER HEL HEA HET V0 V5 V4 V3 V6 PPoint PFirst PSecond PTL PTR PTA)as PResult.
 destruct(code_relation_total M(source_prop_expression IRS_goal6)rho)as(out&HOut).
 exists mt,et,out. refine(conj HMT(conj HET(conj _ (proj1(source_zfr_descriptor_provable M out)(PResult out HOut))))).
 destruct(source_prop_template_binary M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13))out HOut)as(s&m&GS&GM0&HO).
 destruct(source_prop_template_binary M rho SFImpl(SPTSlot 1)(SPTSlot 13)m GM0)as(c&e&GC&GE&HM).
 change(s=code_numeral M(sf_encode named_difference_successor))in GS. change(c=code_numeral M(sf_encode named_difference_closure))in GC. change(e=et)in GE. subst s c e.
 apply(source_prop_template_join M(named_closure_values M et)SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))_ m out eq_refl);[|exact HO].
 exact(source_prop_template_join M(named_closure_values M et)SFImpl(SPTSlot 1)(SPTSlot 2)_ et m eq_refl eq_refl HM).
Qed.
Print Assumptions source_zfr_named_implication_from_point.
