(** Actual An4, child3 and Op4-output0 witness elimination. The only
    input proof is the already constructed pure projection point theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceNumeralLift FixedSourceBounds
 SourceProjectionWitnessShell SourceProjectionNamedOperation SourceProjectionFiniteSyntax SourceProjectionProfilePoint
 SourceFiniteNameParameters SourceFiniteParameters SourceParameterGraphs SourceNamedFiniteCalibration SourceNamedDifferenceCertificates SourceNamedDifferenceFacts
 SourceRepresentationNamedConjunction SourceRepresentationNamedWitness SourceRepresentativeRenaming SourceNamedQuantifierRules SourceNamedVacuityImages SourceNamedElimination
 SourceDescriptorNamedPrograms SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorPrograms SourceSetTheoryDescriptors SourceZFRProvability.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition PNW_values M namedAn namedChild result exAn exChild exTarget i:=match i with
 |0=>code_numeral M(sf_encode named_difference_successor)|1=>code_numeral M(sf_encode named_difference_closure)
 |2=>RNC_member M 4|3=>RNC_member M 3|4=>RNC_member M 0|5=>namedAn|6=>namedChild|7=>result
 |8=>code_numeral M(sf_encode projection_named_operation)|9=>code_numeral M(sf_encode projection_named_exists)
 |10=>exAn|11=>exChild|12=>exTarget|_=>zeroM M end.
Theorem source_zfr_projection_named_witness M repAn repChild namedAn namedChild result op inner body law:
 source_bounded M repAn(code_numeral M 2)->source_bounded M repChild(code_numeral M 2)->source_bounded M result(code_numeral M 2)->
 source_representative_renaming M(code_numeral M 4)repAn namedAn->source_representative_renaming M(code_numeral M 3)repChild namedChild->
 code_relation M(projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M))
  (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)op->
 sf_relation M SFImpl namedAn result inner->sf_relation M SFImpl namedChild inner body->sf_relation M SFImpl op body law->source_zfr_provable M law->
 exists mAn mChild mTarget exAn exChild exTarget out,
 sf_relation M SFAnd(RNC_member M 4)namedAn mAn/\sf_relation M SFAnd(RNC_member M 3)namedChild mChild/\sf_relation M SFAnd(RNC_member M 0)result mTarget/\
 source_named_quantifier M false(code_numeral M 4)mAn exAn/\source_named_quantifier M false(code_numeral M 3)mChild exChild/\source_named_quantifier M false(zeroM M)mTarget exTarget/\
 code_relation M(PNW_values M namedAn namedChild result exAn exChild exTarget)(source_prop_expression PW_result)out/\source_zfr_provable M out.
Proof.
 intros BA BC BT HNA HNC HOp HI HB HL PL.
 assert(EOp:op=code_numeral M(sf_encode projection_named_operation)).
 { exact(code_relation_functional M _ _ _ _ HOp(source_projection_named_operation_graph M)). } subst op.
 destruct(sf_relation_total M SFAnd(RNC_member M 4)namedAn)as(mAn&HAn).
 destruct(sf_relation_total M SFAnd(RNC_member M 3)namedChild)as(mChild&HChild).
 destruct(sf_relation_total M SFAnd(RNC_member M 0)result)as(mTarget&HTarget).
 destruct(source_named_quantifier_total M false(code_numeral M 4)mAn)as(exAn&HExAn).
 destruct(source_named_quantifier_total M false(code_numeral M 3)mChild)as(exChild&HExChild).
 destruct(source_named_quantifier_total M false(zeroM M)mTarget)as(exTarget&HExTarget).
 set(rho:=PNW_values M namedAn namedChild result exAn exChild exTarget).
 assert(GA:code_relation M rho(source_prop_expression PW_left)mAn).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 2)(SPTSlot 5)_ _ mAn eq_refl eq_refl HAn). }
 assert(GC:code_relation M rho(source_prop_expression PW_right)mChild).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 3)(SPTSlot 6)_ _ mChild eq_refl eq_refl HChild). }
 assert(GT:code_relation M rho(source_prop_expression PW_target)mTarget).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 4)(SPTSlot 7)_ _ mTarget eq_refl eq_refl HTarget). }
 set(mOutput:=code_numeral M(sf_encode projection_named_matrix)).
 assert(GO:code_relation M rho(source_prop_expression PW_output)mOutput).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 4)(SPTSlot 8)_ _ mOutput eq_refl eq_refl
  (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode projection_named_operation))). }
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)repAn)as(originalAn&HOriginalAn).
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)repChild)as(originalChild&HOriginalChild).
 pose proof(source_representation_named_witness_bound M(code_numeral M 4)repAn namedAn(RNC_member M 4)originalAn mAn exAn BA
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)HNA(sf_make_numeral M SFMember 4 2)HOriginalAn HAn HExAn)as BExAn.
 pose proof(source_representation_named_witness_bound M(code_numeral M 3)repChild namedChild(RNC_member M 3)originalChild mChild exChild BC
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)HNC(sf_make_numeral M SFMember 3 2)HOriginalChild HChild HExChild)as BExChild.
 pose proof(source_representation_witness_body_bound M result mTarget BT HTarget)as BMTarget.
 pose proof(source_named_quantifier_bound M false(zeroM M)mTarget exTarget(code_numeral M 3)BMTarget HExTarget)as BExTarget.
 assert(BOp:source_bounded M(code_numeral M(sf_encode projection_named_operation))(code_numeral M 8)).
 { apply(source_parameter_graph_bounded M 4 projection_operation4 projection_operation_bound(source_finite_parameter_names 4)
  (projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M))(code_numeral M 8));[|exact(source_projection_named_operation_graph M)].
  intros[|[|[|[|i]]]]v HI' HV;try lia.
  - change(v=code_numeral M 4)in HV. subst v. apply(proj2(fixed_source_numeral_lt_iff M 4 8));lia.
  - change(v=code_numeral M 3)in HV. subst v. apply(proj2(fixed_source_numeral_lt_iff M 3 8));lia.
  - change(v=code_numeral M 1)in HV. subst v. apply(proj2(fixed_source_numeral_lt_iff M 1 8));lia.
  - change(v=zeroM M)in HV. subst v. apply coding_zero_lt_succ. }
 assert(BOutput:source_bounded M mOutput(code_numeral M 8)).
 { apply(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 0)(code_numeral M(sf_encode projection_named_operation))mOutput(code_numeral M 8)(or_introl eq_refl)
  (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode projection_named_operation)))). exact(conj(RNC_member_bound M 0 ltac:(lia))BOp). }
 pose proof(source_named_quantifier_bound M false(zeroM M)mOutput(code_numeral M(sf_encode projection_named_exists))(code_numeral M 8)BOutput(source_projection_named_quantifier M))as BExOp.
 assert(BAll:forall i,source_bounded M(rho i)(code_numeral M 8)).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]];cbn[rho PNW_values].
   - exact(proj1(named_difference_fixed_bounds M)).
   - exact(proj2(named_difference_fixed_bounds M)).
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - exact(RNC_representative_bound M repAn namedAn 4 BA ltac:(lia)HNA).
   - exact(RNC_representative_bound M repChild namedChild 3 BC ltac:(lia)HNC).
   - exact(source_bounded_monotone M result _ _ BT(proj2(fixed_source_numeral_lt_iff M 2 9)ltac:(lia))).
   - exact BOp.
   - exact BExOp.
   - exact(source_bounded_monotone M exAn _ _ BExAn(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact(source_bounded_monotone M exChild _ _ BExChild(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact(source_bounded_monotone M exTarget _ _ BExTarget(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - apply source_bounded_accept_falsity. }
 assert(V0:source_prop_named_vacuity M rho(zeroM M)PW_goal0).
 { cbn[source_prop_named_vacuity PW_goal0 PW_left PW_right rho PNW_values]. repeat split.
   - exact(named_difference_member_vacuous M 0 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repAn namedAn(code_numeral M 4)(zeroM M)BA HNA(source_fixed_numeral_neq M 4 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(named_difference_member_vacuous M 0 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repChild namedChild(code_numeral M 3)(zeroM M)BC HNC(source_fixed_numeral_neq M 3 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 0 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 0 ltac:(auto))).
   - exact(source_named_quantifier_is_vacuous M false(zeroM M)mTarget exTarget(code_numeral M 3)BMTarget HExTarget). }
 assert(V3:source_prop_named_vacuity M rho(code_numeral M 3)PW_goal3).
 { cbn[source_prop_named_vacuity PW_goal3 PW_left rho PNW_values]. repeat split.
   - exact(named_difference_member_vacuous M 3 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repAn namedAn(code_numeral M 4)(code_numeral M 3)BA HNA(source_fixed_numeral_neq M 4 3 ltac:(lia))(source_fixed_numeral_neq M 1 3 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M exTarget(code_numeral M 3)(code_numeral M 3)BExTarget(coding_lt_succ M _)). }
 assert(V4:source_prop_named_vacuity M rho(code_numeral M 4)PW_goal4).
 { cbn[source_prop_named_vacuity PW_goal4 rho PNW_values]. repeat split.
   - exact(proj1(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M exChild(code_numeral M 4)(code_numeral M 3)BExChild(proj2(fixed_source_numeral_lt_iff M 3 5)ltac:(lia))).
   - exact(source_named_vacuous_above_bound M exTarget(code_numeral M 4)(code_numeral M 3)BExTarget(proj2(fixed_source_numeral_lt_iff M 3 5)ltac:(lia))). }
 assert(PPoint:source_descriptor_template M ZFRSourceDescriptor rho PW_point).
 { intros out G. assert(GPoint:code_relation M rho(source_prop_expression PW_point)law).
   { unfold PW_point. apply(source_prop_template_join M rho SFImpl(SPTSlot 8)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 5)(SPTSlot 7)))_ body law eq_refl);[|exact HL].
     apply(source_prop_template_join M rho SFImpl(SPTSlot 6)(SPTImpl(SPTSlot 5)(SPTSlot 7))namedChild inner body eq_refl);[|exact HB].
     exact(source_prop_template_join M rho SFImpl(SPTSlot 5)(SPTSlot 7)namedAn result inner eq_refl eq_refl HI). }
   rewrite(code_relation_functional M _ rho out law G GPoint). exact(proj2(source_zfr_descriptor_provable M law)PL). }
 assert(POperation:source_descriptor_template M ZFRSourceDescriptor rho PW_operation).
 { intros out G. assert(GOp:code_relation M rho(source_prop_expression PW_operation)(code_numeral M(sf_encode projection_named_law))).
   { unfold PW_operation,projection_named_law.
     refine(RNC_fixed_imp_graph M rho named_difference_successor _ (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 9))))eq_refl _).
     refine(RNC_fixed_imp_graph M rho named_difference_closure _ (SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 9)))eq_refl _).
     refine(RNC_fixed_imp_graph M rho($4 ∈' $2)_ (SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 9))eq_refl _).
     exact(RNC_fixed_imp_graph M rho($3 ∈' $2)projection_named_exists(SPTSlot 3)(SPTSlot 9)eq_refl eq_refl). }
   rewrite(code_relation_functional M _ rho out _ G GOp). exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_projection_named_certificate M)). }
 destruct(code_relation_total M(source_prop_expression PW_result)rho)as(out&HOut).
 pose proof(source_descriptor_projection_witness_shell M ZFRSourceDescriptor rho(code_numeral M 8)(zeroM M)(code_numeral M 4)(code_numeral M 3)
  mOutput mAn mChild mTarget out BAll GO GA GC GT(source_projection_named_quantifier M)HExAn HExChild HExTarget V0 V3 V4 PPoint POperation HOut)as POut.
 exists mAn,mChild,mTarget,exAn,exChild,exTarget,out.
 exact(conj HAn(conj HChild(conj HTarget(conj HExAn(conj HExChild(conj HExTarget(conj HOut(proj1(source_zfr_descriptor_provable M out)POut)))))))).
Qed.
Print Assumptions source_zfr_projection_named_witness.
