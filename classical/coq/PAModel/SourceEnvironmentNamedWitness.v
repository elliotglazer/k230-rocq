(** Actual named An witness construction: the old An and the Op3 output
    are eliminated with all finite operation and carrier laws supplied. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNumeralLift SourcePropositionalTemplates SourceDescriptorProvability SourceZFRProvability SourceSetTheoryDescriptors
 SourceEnvironmentWitnessShell SourceNamedEnvironmentCertificate SourceNamedEnvironmentCarrier SourceEnvironmentOperationPadding
 SourceNamedDifferenceCertificates SourceNamedFiniteCalibration SourceNamedDifferenceFacts SourceRepresentationNamedConjunction SourceRepresentationNamedWitness
 SourceNamedVacuity SourceNamedVacuityImages SourceNamedElimination SourceNamedQuantifierRules
 SourceRepresentativeRenaming SourceEnvironmentCarrierClosure FixedSourceBounds.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition ECN_values M named result oldex targetex i:=match i with
 |0=>code_numeral M(sf_encode named_difference_successor)
 |1=>code_numeral M(sf_encode named_difference_closure)
 |2=>RNC_member M 3|3=>RNC_member M 1|4=>RNC_member M 0|5=>named|6=>result
 |7=>code_numeral M(sf_encode environment_named_operation)
 |8=>code_numeral M(sf_encode environment_named_exists)|9=>oldex|10=>targetex|_=>zeroM M end.
Theorem source_zfr_environment_named_witness M previous named result op inner law:
 source_bounded M previous(code_numeral M 2) ->source_bounded M result(code_numeral M 2) ->
 source_representative_renaming M(code_numeral M 3)previous named ->
 source_environment_operation_graph M(code_numeral M 3)op ->
 sf_relation M SFImpl named result inner ->sf_relation M SFImpl op inner law ->source_zfr_provable M law ->
 exists oldbody targetbody oldex targetex out,
 sf_relation M SFAnd(RNC_member M 3)named oldbody /\sf_relation M SFAnd(RNC_member M 0)result targetbody /\
 source_named_quantifier M false(code_numeral M 3)oldbody oldex /\
 source_named_quantifier M false(zeroM M)targetbody targetex /\
 code_relation M(ECN_values M named result oldex targetex)(source_prop_expression ECW_result)out /\source_zfr_provable M out.
Proof.
 intros BP BR HNamed HOp HInner HLaw PLaw.
 assert(EOp:op=code_numeral M(sf_encode environment_named_operation)).
 { exact(code_relation_functional M _ _ op _(HOp)(source_named_environment_operation_graph M)). }
 subst op.
 destruct(sf_relation_total M SFAnd(RNC_member M 3)named)as(oldbody&HOldBody).
 destruct(sf_relation_total M SFAnd(RNC_member M 0)result)as(targetbody&HTargetBody).
 destruct(source_named_quantifier_total M false(code_numeral M 3)oldbody)as(oldex&HOldEx).
 destruct(source_named_quantifier_total M false(zeroM M)targetbody)as(targetex&HTargetEx).
 set(values:=ECN_values M named result oldex targetex).
 pose proof(named_difference_fixed_bounds M)as[BS BC].
 pose proof(RNC_representative_bound M previous named 3 BP ltac:(lia)HNamed)as BN.
 assert(BR8:source_bounded M result(code_numeral M 8)).
 { exact(source_bounded_monotone M result(code_numeral M 2)(code_numeral M 8)BR
   (proj2(fixed_source_numeral_lt_iff M 2 9)ltac:(lia))). }
 assert(BOldBody:source_bounded M oldbody(code_numeral M 8)).
 { exact(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 3)named oldbody _(or_introl eq_refl)HOldBody)
   (conj(RNC_member_bound M 3 ltac:(lia))BN)). }
 assert(BTarget3:source_bounded M targetbody(code_numeral M 3)).
 { exact(source_representation_witness_body_bound M result targetbody BR HTargetBody). }
 pose proof(source_named_quantifier_bound M false(zeroM M)targetbody targetex(code_numeral M 3)BTarget3 HTargetEx)as BTargetEx3.
 pose proof(source_named_quantifier_bound M false(code_numeral M 3)oldbody oldex(code_numeral M 8)BOldBody HOldEx)as BOldEx.
 assert(BOpBody:source_bounded M(code_numeral M(sf_encode environment_named_matrix))(code_numeral M 8)).
 { apply(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 0)(code_numeral M(sf_encode environment_named_operation))
   (code_numeral M(sf_encode environment_named_matrix))(code_numeral M 8)(or_introl eq_refl)
   (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode environment_named_operation)))).
   exact(conj(RNC_member_bound M 0 ltac:(lia))(source_named_environment_operation_bound M)). }
 pose proof(source_named_quantifier_bound M false(zeroM M)(code_numeral M(sf_encode environment_named_matrix))
  (code_numeral M(sf_encode environment_named_exists))(code_numeral M 8)BOpBody(source_named_environment_exists_graph M))as BOpEx.
 assert(BTargetEx:source_bounded M targetex(code_numeral M 8)).
 { exact(source_bounded_monotone M targetex(code_numeral M 3)(code_numeral M 8)BTargetEx3
   (proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))). }
 assert(BValues:forall i,source_bounded M(values i)(code_numeral M 8)).
 { intros[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]];cbn[values ECN_values].
   - exact BS.
   - exact BC.
   - exact(RNC_member_bound M 3 ltac:(lia)).
   - exact(RNC_member_bound M 1 ltac:(lia)).
   - exact(RNC_member_bound M 0 ltac:(lia)).
   - exact BN.
   - exact BR8.
   - exact(source_named_environment_operation_bound M).
   - exact BOpEx.
   - exact BOldEx.
   - exact BTargetEx.
   - apply source_bounded_accept_falsity. }
 assert(GOpBody:code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 7)))
  (code_numeral M(sf_encode environment_named_matrix))).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|].
   exact(sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode environment_named_operation)). }
 assert(GOldBody:code_relation M values(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 5)))oldbody).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HOldBody]. }
 assert(GTargetBody:code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 6)))targetbody).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HTargetBody]. }
 assert(GPoint:code_relation M values(source_prop_expression ECW_point)law).
 { eapply environment_carrier_code_join;[reflexivity| |exact HLaw].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HInner]. }
 assert(GOp:code_relation M values(source_prop_expression ECW_op)(code_numeral M(sf_encode
  (named_difference_successor→named_difference_closure→($3 ∈' $2)→($1 ∈' $2)→environment_named_exists)))).
 { unfold ECW_op.
   refine(RNC_fixed_imp_graph M values named_difference_successor
    (named_difference_closure→($3 ∈' $2)→($1 ∈' $2)→environment_named_exists)
    (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 8))))eq_refl _).
   refine(RNC_fixed_imp_graph M values named_difference_closure
    (($3 ∈' $2)→($1 ∈' $2)→environment_named_exists)
    (SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 8)))eq_refl _).
   refine(RNC_fixed_imp_graph M values($3 ∈' $2)(($1 ∈' $2)→environment_named_exists)
    (SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 8))eq_refl _).
   exact(RNC_fixed_imp_graph M values($1 ∈' $2)environment_named_exists(SPTSlot 3)(SPTSlot 8)eq_refl eq_refl). }
 assert(GCarrier:code_relation M values(source_prop_expression ECW_carrier)(code_numeral M(sf_encode
  (named_difference_successor→named_difference_closure→($1 ∈' $2))))).
 { unfold ECW_carrier.
   refine(RNC_fixed_imp_graph M values named_difference_successor(named_difference_closure→($1 ∈' $2))
    (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3))eq_refl _).
   exact(RNC_fixed_imp_graph M values named_difference_closure($1 ∈' $2)(SPTSlot 1)(SPTSlot 3)eq_refl eq_refl). }
 pose proof(named_difference_conditions_vacuous M 0(or_introl eq_refl))as[VS0 VC0].
 pose proof(named_difference_conditions_vacuous M 3(or_intror(or_introl eq_refl)))as[VS3 VC3].
 assert(VNamed:source_named_vacuous M(zeroM M)named).
 { exact(source_named_vacuous_representative_image M previous named(code_numeral M 3)(zeroM M)BP HNamed
   (source_fixed_numeral_neq M 3 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))). }
 pose proof(source_named_quantifier_is_vacuous M false(zeroM M)targetbody targetex(code_numeral M 3)BTarget3 HTargetEx)as VTarget0.
 pose proof(source_named_vacuous_above_bound M targetex(code_numeral M 3)(code_numeral M 3)BTargetEx3
  (coding_lt_succ M(code_numeral M 3)))as VTarget3.
 destruct(code_relation_total M(source_prop_expression ECW_result)values)as(out&HOut).
 exists oldbody,targetbody,oldex,targetex,out. refine(conj HOldBody(conj HTargetBody(conj HOldEx(conj HTargetEx(conj HOut _))))).
 apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_environment_witness_shell M ZFRSourceDescriptor values(code_numeral M 3)(zeroM M)
  (code_numeral M(sf_encode environment_named_matrix))oldbody targetbody out(code_numeral M 8)
  BValues GOpBody GOldBody GTargetBody(source_named_environment_exists_graph M)HOldEx HTargetEx
  VS0 VC0 VNamed VTarget0 VS3 VC3 VTarget3).
 - intros f HF. rewrite(code_relation_functional M _ values f law HF GPoint). exact(proj2(source_zfr_descriptor_provable M law)PLaw).
 - intros f HF. rewrite(code_relation_functional M _ values f _ HF GOp).
   exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_environment_certificate M)).
 - intros f HF. rewrite(code_relation_functional M _ values f _ HF GCarrier).
   exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_environment_carrier M)).
 - exact HOut.
Qed.
Print Assumptions source_zfr_environment_named_witness.

