(** The positive witness-bound implication.  The actual two existential
    hierarchy witnesses are eliminated by the source calculus, and every
    finite hierarchy theorem is supplied by its checked ZFR certificate. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceOrdinalPredicate SourceLFixed SourceDomainInstances
  NumericalRenaming NumericalInstantiation SourceQuantifierRules SourceInstantiationConstructors
  SourceImplicationAllShift SourceRelativizationRules SourceRelativizationBounds
  SourceHierarchyWitnessShell SourceD0Recipe SourceWitnessBoundGoal SourceWitnessBoundShift SourceFiniteCutoffShift
  SourceCutoffInstantiation SourcePositiveWitnessZFR SourcePositiveWitnessGoal SourceWitnessProofComposition
  SourceWitnessBoundPrograms SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code source_L_domain source_L_domain_code.

Theorem source_zfr_witness_bound_positive M phi g ordinal test goal target result k :
  source_bounded M phi(succM M k) ->coding_lt M g k ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  sr_quantifier M false(source_L_domain_code M)phi test ->
  source_witness_bound_goal M(source_L_domain_code M)phi goal ->
  sf_relation M SFImpl ordinal goal target ->sf_relation M SFImpl test target result ->
  source_zfr_provable M result.
Proof.
  intros HB HG HOrd HTest HGoal HTarget HResult.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(source_witness_bound_goal_bounded M(source_L_domain_code M)phi goal k HD HB HGoal) as HGoalB.
  pose proof(source_guarded_exists_bounded M(source_L_domain_code M)phi test k
    (sr_domain_bound_succ M(source_L_domain_code M)k HD)HB HTest) as HTestB.
  destruct HTest as(testBody&HTestBody&HTestEx).
  destruct(source_cutoff_shift_total M 1 phi) as(p1&HC1).
  destruct(source_cutoff_shift_total M 1 p1) as(p2&HC2).
  destruct(source_cutoff_shift_total M 1 p2) as(p3&HC3).
  pose proof(source_cutoff_shift_bounded M 1 phi p1 k HB HC1) as HB1.
  pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M k)HB1 HC2) as HB2.
  pose proof(source_cutoff_shift_bounded M 1 p2 p3(succM M(succM M k))HB2 HC3) as HB3.
  destruct(numerical_renaming_total M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(phi1&HS1).
  destruct(numerical_renaming_total M phi1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(phi2&HS2).
  pose proof(source_shift_bound M phi phi1(succM M k)HB HS1) as HPhi1B.
  pose proof(source_shift_bound M phi1 phi2(succM M(succM M k))HPhi1B HS2) as HPhi2B.
  pose proof(source_cutoff_thrice_specialization_two M phi p1 p2 p3 phi1 phi2 k HB HC1 HC2 HC3 HS1 HS2) as HInstance.
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal1&HG1).
  destruct(numerical_renaming_total M goal1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal2&HG2).
  destruct(numerical_renaming_total M goal2(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal3&HG3).
  pose proof(source_witness_bound_goal_shift M(source_L_domain_code M)phi p1 goal goal1(succM M k)
    HD HB HC1 HGoal HG1) as HGoal1.
  pose proof(source_witness_bound_goal_shift M(source_L_domain_code M)p1 p2 goal1 goal2(succM M(succM M k))
    HD HB1 HC2 HGoal1 HG2) as HGoal2.
  pose proof(source_witness_bound_goal_shift M(source_L_domain_code M)p2 p3 goal2 goal3
    (succM M(succM M(succM M k)))HD HB2 HC3 HGoal2 HG3) as HGoal3.
  pose proof(source_witness_bound_goal_bounded M(source_L_domain_code M)p1 goal1(succM M k)HD HB1 HGoal1) as HGoal1B.
  pose proof(source_witness_bound_goal_bounded M(source_L_domain_code M)p2 goal2(succM M(succM M k))HD HB2 HGoal2) as HGoal2B.
  pose proof(source_witness_bound_goal_bounded M(source_L_domain_code M)p3 goal3(succM M(succM M(succM M k)))
    HD HB3 HGoal3) as HGoal3B.
  destruct(source_zfr_hierarchy_above_shell M(zeroM M)(succM M g))
    as(ly&og&exD&bodyD&bodyY&od&subset&pair0&level&inner0&member&tail&above&HAbove&PAbove).
  destruct HAbove as(HLY&HOG&HOD&HLevel&HMember&HPair0&HInner0&HBodyY&HBodyD&HExD&HTail&HAbove).
  pose proof(numerical_instantiation_functional M(source_L_domain_code M)(zeroM M)ly(source_L_domain_code M)
    HLY(source_domain_instance_zero M(source_L_domain_code M)HD)) as E. subst ly.
  destruct(source_zfr_provable_has_bound M above PAbove) as(bound&HAboveB).
  destruct(proj1(source_bounded_accept_binary M SFImpl(source_L_domain_code M)tail above bound
    (or_intror(or_intror eq_refl))HAbove)HAboveB) as(HLYB&HTailB).
  destruct(proj1(source_bounded_accept_binary M SFImpl og exD tail bound
    (or_intror(or_intror eq_refl))HTail)HTailB) as(HOGB&HExDB).
  pose proof(proj1(source_bounded_accept_unary M SFEx bodyD exD bound(or_intror eq_refl)HExD)HExDB) as HBodyDB.
  pose proof(proj1(source_bounded_accept_unary M SFEx bodyY bodyD(succM M bound)(or_intror eq_refl)HBodyD)HBodyDB) as HBodyYB.
  destruct(proj1(source_bounded_accept_binary M SFAnd inner0 member bodyY(succM M(succM M bound))
    (or_introl eq_refl)HBodyY)HBodyYB) as(HInner0B&HMemberB).
  destruct(proj1(source_bounded_accept_binary M SFAnd pair0 level inner0(succM M(succM M bound))
    (or_introl eq_refl)HInner0)HInner0B) as(HPair0B&HLevelB).
  destruct(proj1(source_bounded_accept_binary M SFAnd od subset pair0(succM M(succM M bound))
    (or_introl eq_refl)HPair0)HPair0B) as(HODB&HSubsetB).
  destruct(sf_relation_total M SFAnd od level) as(pair&HPair).
  destruct(sf_relation_total M SFAnd pair member) as(inner&HInner).
  destruct(sf_relation_total M SFAnd inner phi2) as(body&HBody).
  destruct(sf_relation_total M SFImpl body goal3) as(positive&HPositive).
  assert(H0:coding_lt M(zeroM M)(succM M(succM M(succM M k)))) by apply coding_zero_lt_succ.
  assert(H1:coding_lt M(code_numeral M 1)(succM M(succM M(succM M k)))).
  { apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M(succM M k)))). apply coding_zero_lt_succ. }
  assert(H2:coding_lt M(code_numeral M 2)(succM M(succM M(succM M k)))).
  { apply(proj2(coding_lt_succ_cancel M(code_numeral M 1)(succM M(succM M k)))).
    apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))). apply coding_zero_lt_succ. }
  pose proof(source_zfr_positive_witness_goal M(source_L_domain_code M)p3(code_numeral M 1)(code_numeral M 2)
    (zeroM M)od level member phi2 body goal3 positive(succM M(succM M(succM M k)))
    HD HB3 H1 H2 H0 HOD HLevel HMember HInstance
    (ex_intro _ pair(ex_intro _ inner(conj HPair(conj HInner HBody))))HGoal3 HPositive) as PPositive.
  destruct(sf_relation_total M SFImpl phi2 goal3) as(point3&HPoint3).
  destruct(sf_relation_total M SFImpl bodyY point3) as(witnessY&HWitnessY).
  set(rho6:=source_witness_six_environment od subset level member phi2 goal3).
  assert(HBounds6:forall i,source_bounded M(rho6 i)
    (addM M(succM M(succM M bound))(succM M(succM M(succM M k))))).
  { assert(Left:forall f,source_bounded M f(succM M(succM M bound)) ->
      source_bounded M f(addM M(succM M(succM M bound))(succM M(succM M(succM M k))))).
    { intros f HF. exact(source_bounded_monotone M f _ _ HF(coding_le_add M _ _)). }
    assert(Right:forall f,source_bounded M f(succM M(succM M(succM M k))) ->
      source_bounded M f(addM M(succM M(succM M bound))(succM M(succM M(succM M k))))).
    { intros f HF. apply(source_bounded_monotone M f _ _ HF). rewrite Arithmetic.add_comm. apply coding_le_add. }
    intros[|[|[|[|[|i]]]]];cbn[rho6 source_witness_six_environment].
    all:first[apply Left;assumption|apply Right;assumption]. }
  assert(HPositiveGraph:code_relation M rho6(source_prop_expression witness_positive_input)positive).
  { unfold witness_positive_input,source_prop_expression,rho6,source_witness_six_environment. functionality_graph. }
  assert(HWitnessYGraph:code_relation M rho6(source_prop_expression witness_positive_output)witnessY).
  { unfold witness_positive_output,witness_positive_body,source_prop_expression,rho6,source_witness_six_environment.
    functionality_graph. }
  pose proof(source_zfr_prop_one M _ _ source_witness_positive_rearrangement rho6 _ positive witnessY
    HBounds6 HPositiveGraph HWitnessYGraph PPositive) as PWitnessY.
  destruct(sf_relation_total M SFImpl phi1 goal2) as(point2&HPoint2).
  pose proof(source_implication_shift_graph M phi1 goal2 point2 phi2 goal3 point3 HPoint2 HPoint3 HS2 HG3) as HPoint2Shift.
  assert(HPoint2B:source_bounded M point2(succM M(succM M k))).
  { exact(proj2(source_bounded_accept_binary M SFImpl phi1 goal2 point2(succM M(succM M k))
      (or_intror(or_intror eq_refl))HPoint2)(conj HPhi1B HGoal2B)). }
  destruct(sf_relation_total M SFImpl bodyD point2) as(witnessD&HWitnessD).
  pose proof(source_zfr_exists_implication M bodyY bodyD point2 point3 witnessY witnessD(succM M bound)
    (succM M(succM M k))HBodyDB HPoint2B HBodyD HPoint2Shift HWitnessY HWitnessD PWitnessY) as PWitnessD.
  destruct(sf_relation_total M SFImpl phi goal1) as(point1&HPoint1).
  pose proof(source_implication_shift_graph M phi goal1 point1 phi1 goal2 point2 HPoint1 HPoint2 HS1 HG2) as HPoint1Shift.
  assert(HPoint1B:source_bounded M point1(succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFImpl phi goal1 point1(succM M k)
      (or_intror(or_intror eq_refl))HPoint1)(conj HB HGoal1B)). }
  destruct(sf_relation_total M SFImpl exD point1) as(fromAbove&HFromAbove).
  pose proof(source_zfr_exists_implication M bodyD exD point1 point2 witnessD fromAbove bound(succM M k)
    HExDB HPoint1B HExD HPoint1Shift HWitnessD HFromAbove PWitnessD) as PFromAbove.
  destruct(sf_relation_total M SFImpl og goal1) as(shiftedTarget&HShiftedTarget).
  destruct(sf_relation_total M SFImpl testBody shiftedTarget) as(witnessTest&HWitnessTest).
  set(rho5:=source_witness_five_environment(source_L_domain_code M)og exD phi goal1).
  assert(HBounds5:forall i,source_bounded M(rho5 i)(addM M bound(succM M k))).
  { assert(Left:forall f,source_bounded M f bound ->source_bounded M f(addM M bound(succM M k))).
    { intros f HF. exact(source_bounded_monotone M f _ _ HF(coding_le_add M _ _)). }
    assert(Right:forall f,source_bounded M f(succM M k) ->source_bounded M f(addM M bound(succM M k))).
    { intros f HF. apply(source_bounded_monotone M f _ _ HF). rewrite Arithmetic.add_comm. apply coding_le_add. }
    intros[|[|[|[|i]]]];cbn[rho5 source_witness_five_environment].
    all:first[apply Left;assumption|apply Right;assumption]. }
  assert(HAboveGraph:code_relation M rho5(source_prop_expression witness_above_input)above).
  { unfold witness_above_input,source_prop_expression,rho5,source_witness_five_environment. functionality_graph. }
  assert(HFromAboveGraph:code_relation M rho5(source_prop_expression witness_existential_input)fromAbove).
  { unfold witness_existential_input,source_prop_expression,rho5,source_witness_five_environment. functionality_graph. }
  assert(HWitnessTestGraph:code_relation M rho5(source_prop_expression witness_above_output)witnessTest).
  { unfold witness_above_output,source_prop_expression,rho5,source_witness_five_environment. functionality_graph. }
  pose proof(source_zfr_prop_two M _ _ _ source_witness_above_application rho5 _ above fromAbove witnessTest
    HBounds5 HAboveGraph HFromAboveGraph HWitnessTestGraph PAbove PFromAbove) as PWitnessTest.
  destruct(numerical_renaming_total M ordinal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(os&HOS).
  pose proof(source_domain_instance_shift M(source_ordinal_predicate_code M)g ordinal os
    (source_ordinal_predicate_bounded M)HOrd HOS) as HOSG.
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(succM M g)os og HOSG HOG) as E.
  subst os.
  pose proof(source_implication_shift_graph M ordinal goal target og goal1 shiftedTarget HTarget HShiftedTarget HOS HG1) as HTShift.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal k
    (source_ordinal_predicate_bounded M)HG HOrd) as HOrdinalB.
  assert(HTargetB:source_bounded M target k).
  { exact(proj2(source_bounded_accept_binary M SFImpl ordinal goal target k
      (or_intror(or_intror eq_refl))HTarget)(conj HOrdinalB HGoalB)). }
  exact(source_zfr_exists_implication M testBody test target shiftedTarget witnessTest result k k
    HTestB HTargetB HTestEx HTShift HWitnessTest HResult PWitnessTest).
Qed.

Print Assumptions source_zfr_witness_bound_positive.
