(** Assemble actual named atom witnesses while retaining the internally
    coded matrices. The three existence proof inputs are consumed by
    actual named existential elimination, not postulated as a profile. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNumeralLift FixedSourceBounds SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorNamedPrograms
 SourceAtomicWitnessShell SourceAtomicNamedCertificates SourceAtomicUnaryInstance SourceAtomicCondition SourceAtomicOperationSyntax
 SourceNamedQuantifierRules SourceNamedVacuity SourceNamedElimination SourceNamedVacuityImages
 SourceNamedFiniteCalibration SourceNamedDifferenceCertificates SourceNamedDifferenceFacts SourceRepresentationNamedConjunction
 SourceRepresentationNamedWitness SourceRepresentativeRenaming SourceNamedClosureExistence
 NumericalInstantiation SourceDomainInstances SourceZFRProvability SourceSetTheoryDescriptors SourceParameterGraphs SourceFiniteNameParameters.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope minZFsyn.
Unset Implicit Arguments.
Local Opaque code_numeral.
Definition AWN_member M i:=code_numeral M(sf_make SFMember i 2).
Definition AWN_operation M member:=code_numeral M(sf_encode(named_atomic_operation member)).
Definition AWN_opex M member:=code_numeral M(sf_encode(named_atomic_exists member)).
Definition AWN_environment M member an ni nj rep ea ei ej et i:=match i with
 |0=>code_numeral M(sf_encode named_difference_successor)|1=>code_numeral M(sf_encode named_difference_closure)
 |2=>AWN_member M 3|3=>AWN_member M 4|4=>AWN_member M 5|5=>AWN_member M 0
 |6=>an|7=>ni|8=>nj|9=>AWN_operation M member|10=>rep|11=>AWN_opex M member
 |12=>ea|13=>ei|14=>ej|15=>et|_=>zeroM M end.
Lemma AWN_closure_template M T rho index ex out:
 rho 0=code_numeral M(sf_encode named_difference_successor)->rho 1=code_numeral M(sf_encode named_difference_closure)->rho index=ex->
 code_relation M(named_closure_values M ex)(source_prop_expression NCE_template)out->
 source_descriptor_provable M T out->
 source_descriptor_template M T rho(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot index))).
Proof.
 intros HS HC HE HOut POut f HF.
 destruct(source_prop_template_binary M _ SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))out HOut)
  as(s&middle&GS&GM&HO).
 change(s=code_numeral M(sf_encode named_difference_successor))in GS. subst s.
 destruct(source_prop_template_binary M _ SFImpl(SPTSlot 1)(SPTSlot 2)middle GM)as(c&e&GC&GE&HM).
 change(c=code_numeral M(sf_encode named_difference_closure))in GC. change(e=ex)in GE. subst c e.
 assert(G:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot index))))out).
 { apply(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot index))(rho 0)middle out eq_refl);[|now rewrite HS].
   apply(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot index)(rho 1)(rho index)middle eq_refl eq_refl).
   now rewrite HC,HE. }
 rewrite(code_relation_functional M _ rho f out HF G). exact POut.
Qed.
Theorem source_zfr_atomic_named_witnesses M member an numI numJ namedA ni nj rep condition inner law ea ei ej ma mi mj outA outI outJ:
 source_bounded M an(code_numeral M 2)->source_bounded M numI(code_numeral M 1)->source_bounded M numJ(code_numeral M 1)->source_bounded M rep(code_numeral M 2)->
 source_representative_renaming M(code_numeral M 3)an namedA->
 numerical_instantiation M numI(code_numeral M 4)ni->numerical_instantiation M numJ(code_numeral M 5)nj->
 source_atomic_condition_names M member numI numJ(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(zeroM M)condition->
 sf_relation M SFImpl namedA rep inner->sf_relation M SFImpl condition inner law->source_zfr_provable M law->
 sf_relation M SFAnd(AWN_member M 3)namedA ma->sf_relation M SFAnd(AWN_member M 4)ni mi->sf_relation M SFAnd(AWN_member M 5)nj mj->
 source_named_quantifier M false(code_numeral M 3)ma ea->source_named_quantifier M false(code_numeral M 4)mi ei->source_named_quantifier M false(code_numeral M 5)mj ej->
 code_relation M(named_closure_values M ea)(source_prop_expression NCE_template)outA->source_zfr_provable M outA->
 code_relation M(named_closure_values M ei)(source_prop_expression NCE_template)outI->source_zfr_provable M outI->
 code_relation M(named_closure_values M ej)(source_prop_expression NCE_template)outJ->source_zfr_provable M outJ->
 exists mt et out,sf_relation M SFAnd(AWN_member M 0)rep mt/\source_named_quantifier M false(zeroM M)mt et/\
 code_relation M(named_closure_values M et)(source_prop_expression NCE_template)out/\source_zfr_provable M out.
Proof.
 intros BA BI BJ BR HNA HNI HNJ HC HInner HLaw PLaw HMA HMI HMJ HEA HEI HEJ GA PA GI PI GJ PJ.
 pose proof(source_unary_instance_representative M numI(code_numeral M 4)ni BI HNI)as RNI.
 pose proof(source_unary_instance_representative M numJ(code_numeral M 5)nj BJ HNJ)as RNJ.
 assert(BI2:source_bounded M numI(code_numeral M 2))by(exact(source_bounded_monotone M _ _ _ BI(proj2(fixed_source_numeral_lt_iff M 1 3)ltac:(lia)))).
 assert(BJ2:source_bounded M numJ(code_numeral M 2))by(exact(source_bounded_monotone M _ _ _ BJ(proj2(fixed_source_numeral_lt_iff M 1 3)ltac:(lia)))).
 destruct(sf_relation_total M SFAnd(AWN_member M 0)rep)as(mt&HMT).
 destruct(source_named_quantifier_total M false(zeroM M)mt)as(et&HET).
 set(rho:=AWN_environment M member namedA ni nj rep ea ei ej et).
 assert(GA0:code_relation M rho(source_prop_expression AWS_An)ma)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 2)(SPTSlot 6)(rho 2)(rho 6)ma eq_refl eq_refl HMA)).
 assert(GI0:code_relation M rho(source_prop_expression AWS_Ni)mi)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 3)(SPTSlot 7)(rho 3)(rho 7)mi eq_refl eq_refl HMI)).
 assert(GJ0:code_relation M rho(source_prop_expression AWS_Nj)mj)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 4)(SPTSlot 8)(rho 4)(rho 8)mj eq_refl eq_refl HMJ)).
 assert(GT:code_relation M rho(source_prop_expression AWS_Target)mt)by(exact(source_prop_template_join M rho SFAnd(SPTSlot 5)(SPTSlot 10)(rho 5)(rho 10)mt eq_refl eq_refl HMT)).
 set(mop:=code_numeral M(sf_encode(named_atomic_matrix member))).
 assert(GO:code_relation M rho(source_prop_expression AWS_Op)mop).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 5)(SPTSlot 9)(rho 5)(rho 9)mop eq_refl eq_refl(sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode(named_atomic_operation member)))). }
 assert(BMT:source_bounded M mt(code_numeral M 3))by(exact(source_representation_witness_body_bound M rep mt BR HMT)).
 pose proof(source_named_quantifier_bound M false(zeroM M)mt et(code_numeral M 3)BMT HET)as BET.
 assert(BA8:source_bounded M namedA(code_numeral M 8))by(exact(RNC_representative_bound M an namedA 3 BA ltac:(lia)HNA)).
 assert(BI8:source_bounded M ni(code_numeral M 8))by(exact(RNC_representative_bound M numI ni 4 BI2 ltac:(lia)RNI)).
 assert(BJ8:source_bounded M nj(code_numeral M 8))by(exact(RNC_representative_bound M numJ nj 5 BJ2 ltac:(lia)RNJ)).
 assert(BO8:source_bounded M(AWN_operation M member)(code_numeral M 8)).
 { apply(source_parameter_graph_bounded M 4(source_atomic_operation_predicate member)(source_atomic_operation_finite_bound member)
    (source_finite_parameter_names 4)(source_atomic_operation_environment(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(zeroM M))(code_numeral M 8));[|apply named_atomic_operation_graph].
   intros[|[|[|[|idx]]]]v HV HN;try lia.
   - change(v=code_numeral M 3)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 3 8));lia.
   - change(v=code_numeral M 4)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 4 8));lia.
   - change(v=code_numeral M 5)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 5 8));lia.
   - change(v=zeroM M)in HN. subst v. exact(proj2(fixed_source_numeral_lt_iff M 0 8)ltac:(lia)). }
 assert(BMop:source_bounded M mop(code_numeral M 8)).
 { exact(proj2(source_bounded_accept_binary M SFAnd(AWN_member M 0)(AWN_operation M member)mop(code_numeral M 8)(or_introl eq_refl)
    (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode(named_atomic_operation member))))(conj(RNC_member_bound M 0 ltac:(lia))BO8)). }
 pose proof(source_named_quantifier_bound M false(zeroM M)mop(AWN_opex M member)(code_numeral M 8)BMop(named_atomic_quantifier M member))as BEO.
 assert(BEA:source_bounded M ea(code_numeral M 8)).
 { exact(source_named_quantifier_bound M false(code_numeral M 3)ma ea(code_numeral M 8)
   (proj2(source_bounded_accept_binary M SFAnd _ _ _ _ (or_introl eq_refl)HMA)(conj(RNC_member_bound M 3 ltac:(lia))BA8))HEA). }
 assert(BEI:source_bounded M ei(code_numeral M 8)).
 { exact(source_named_quantifier_bound M false(code_numeral M 4)mi ei(code_numeral M 8)
   (proj2(source_bounded_accept_binary M SFAnd _ _ _ _ (or_introl eq_refl)HMI)(conj(RNC_member_bound M 4 ltac:(lia))BI8))HEI). }
 assert(BEJ:source_bounded M ej(code_numeral M 8)).
 { exact(source_named_quantifier_bound M false(code_numeral M 5)mj ej(code_numeral M 8)
   (proj2(source_bounded_accept_binary M SFAnd _ _ _ _ (or_introl eq_refl)HMJ)(conj(RNC_member_bound M 5 ltac:(lia))BJ8))HEJ). }
 assert(BAll:forall idx,source_bounded M(rho idx)(code_numeral M 8)).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|idx]]]]]]]]]]]]]]]];cbn[rho AWN_environment].
   - exact(proj1(named_difference_fixed_bounds M)).
   - exact(proj2(named_difference_fixed_bounds M)).
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - exact BA8.
   - exact BI8.
   - exact BJ8.
   - exact BO8.
   - exact(source_bounded_monotone M _ _ _ BR(proj2(fixed_source_numeral_lt_iff M 2 9)ltac:(lia))).
   - exact BEO.
   - exact BEA.
   - exact BEI.
   - exact BEJ.
   - exact(source_bounded_monotone M _ _ _ BET(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - apply source_bounded_accept_falsity. }
 assert(V0:source_prop_named_vacuity M rho(zeroM M)AWS_goal0).
 { cbn[source_prop_named_vacuity AWS_goal0 AWS_An AWS_Ni AWS_Nj rho AWN_environment]. repeat split.
   - exact(named_difference_member_vacuous M 0 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M an namedA(code_numeral M 3)(zeroM M)BA HNA(source_fixed_numeral_neq M 3 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(named_difference_member_vacuous M 0 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M numI ni(code_numeral M 4)(zeroM M)BI2 RNI(source_fixed_numeral_neq M 4 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(named_difference_member_vacuous M 0 5 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M numJ nj(code_numeral M 5)(zeroM M)BJ2 RNJ(source_fixed_numeral_neq M 5 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(source_named_quantifier_is_vacuous M false(zeroM M)mt et(code_numeral M 3)BMT HET). }
 assert(V5:source_prop_named_vacuity M rho(code_numeral M 5)AWS_goal5).
 { cbn[source_prop_named_vacuity AWS_goal5 AWS_An AWS_Ni rho AWN_environment]. repeat split.
   - exact(named_difference_member_vacuous M 5 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M an namedA(code_numeral M 3)(code_numeral M 5)BA HNA(source_fixed_numeral_neq M 3 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(named_difference_member_vacuous M 5 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M numI ni(code_numeral M 4)(code_numeral M 5)BI2 RNI(source_fixed_numeral_neq M 4 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 5 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 5 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 5)(code_numeral M 3)BET(proj2(fixed_source_numeral_lt_iff M 3 6)ltac:(lia))). }
 assert(V4:source_prop_named_vacuity M rho(code_numeral M 4)AWS_goal4).
 { cbn[source_prop_named_vacuity AWS_goal4 AWS_An rho AWN_environment]. repeat split.
   - exact(named_difference_member_vacuous M 4 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M an namedA(code_numeral M 3)(code_numeral M 4)BA HNA(source_fixed_numeral_neq M 3 4 ltac:(lia))(source_fixed_numeral_neq M 1 4 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 4)(code_numeral M 3)BET(proj2(fixed_source_numeral_lt_iff M 3 5)ltac:(lia))). }
 assert(V3:source_prop_named_vacuity M rho(code_numeral M 3)AWS_goal3).
 { cbn[source_prop_named_vacuity AWS_goal3 rho AWN_environment]. repeat split.
   - exact(proj1(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 3)(code_numeral M 3)BET(coding_lt_succ M(code_numeral M 3))). }
 assert(PPoint:source_descriptor_template M ZFRSourceDescriptor rho AWS_point).
 { intros f HF. destruct HC as(ni'&nj'&op&nums&HNI'&HNJ'&HOp&HNums&HO).
   assert(ni'=ni)by(eapply numerical_instantiation_functional;eassumption). subst ni'.
   assert(nj'=nj)by(eapply numerical_instantiation_functional;eassumption). subst nj'.
   assert(op=AWN_operation M member)by(exact(code_relation_functional M _ _ op _ HOp(named_atomic_operation_graph M member))). subst op.
   assert(G:code_relation M rho(source_prop_expression AWS_point)law).
   { apply(source_prop_template_join M rho SFImpl(SPTAnd(SPTSlot 9)(SPTAnd(SPTSlot 7)(SPTSlot 8)))(SPTImpl(SPTSlot 6)(SPTSlot 10))condition inner law);[| |exact HLaw].
     - apply(source_prop_template_join M rho SFAnd(SPTSlot 9)(SPTAnd(SPTSlot 7)(SPTSlot 8))(rho 9)nums condition eq_refl);[|exact HO].
       exact(source_prop_template_join M rho SFAnd(SPTSlot 7)(SPTSlot 8)ni nj nums eq_refl eq_refl HNums).
     - exact(source_prop_template_join M rho SFImpl(SPTSlot 6)(SPTSlot 10)namedA rep inner eq_refl eq_refl HInner). }
   rewrite(code_relation_functional M _ rho f law HF G). exact(proj2(source_zfr_descriptor_provable M law)PLaw). }
 assert(POp:source_descriptor_template M ZFRSourceDescriptor rho AWS_operation).
 { intros f HF. assert(G:code_relation M rho(source_prop_expression AWS_operation)(code_numeral M(sf_encode
    (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→($5 ∈' $2)→named_atomic_exists member)))).
   { unfold AWS_operation. repeat apply RNC_fixed_imp_graph;reflexivity. }
   rewrite(code_relation_functional M _ rho f _ HF G). exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_atomic_certificate M member)). }
 pose proof(AWN_closure_template M ZFRSourceDescriptor rho 12 ea outA eq_refl eq_refl eq_refl GA(proj2(source_zfr_descriptor_provable M outA)PA))as PTA.
 pose proof(AWN_closure_template M ZFRSourceDescriptor rho 13 ei outI eq_refl eq_refl eq_refl GI(proj2(source_zfr_descriptor_provable M outI)PI))as PTI.
 pose proof(AWN_closure_template M ZFRSourceDescriptor rho 14 ej outJ eq_refl eq_refl eq_refl GJ(proj2(source_zfr_descriptor_provable M outJ)PJ))as PTJ.
 pose proof(source_descriptor_atomic_witness_shell M ZFRSourceDescriptor rho(code_numeral M 8)(zeroM M)(code_numeral M 5)(code_numeral M 4)(code_numeral M 3)
  ma mi mj mop mt BAll GA0 GI0 GJ0 GO GT(named_atomic_quantifier M member)HEA HEI HEJ HET V0 V5 V4 V3 PPoint POp PTA PTI PTJ)as PResult.
 destruct(code_relation_total M(source_prop_expression AWS_goal3)rho)as(out&HOut).
 exists mt,et,out. refine(conj HMT(conj HET(conj _ (proj1(source_zfr_descriptor_provable M out)(PResult out HOut))))).
 destruct(source_prop_template_binary M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 15))out HOut)as(s&m&GS&GM&HO).
 destruct(source_prop_template_binary M rho SFImpl(SPTSlot 1)(SPTSlot 15)m GM)as(c&e&GC&GE&HM).
 change(s=code_numeral M(sf_encode named_difference_successor))in GS. change(c=code_numeral M(sf_encode named_difference_closure))in GC. change(e=et)in GE. subst s c e.
 apply(source_prop_template_join M (named_closure_values M et)SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))_ m out eq_refl);[|exact HO].
 exact(source_prop_template_join M (named_closure_values M et)SFImpl(SPTSlot 1)(SPTSlot 2)_ et m eq_refl eq_refl HM).
Qed.
Print Assumptions source_zfr_atomic_named_witnesses.
