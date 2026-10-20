(** The empty PCf table has an actual ordinal bound, obtained from the
    fixed successor-container theorem and ordinary source ExE/ExI. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceRelativizationBounds NumericalContexts NumericalEnvironments NumericalSourceFull NumericalRenaming NumericalInstantiation
  SourceDomainInstances SourceOrdinalPredicate SourceHierarchySyntax SourceQuantifierRules SourcePieceConjunction
  SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundRenaming SourcePieceBoundIntroduction SourcePieceBoundMaxJoint
  SourceSuccessorContainerTotal SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability
  SourceWitnessProofComposition SourceCBSuccessor SourcePropositionalTemplates.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Lemma source_piece_table_valid_zero M sb sc:source_piece_table_valid M sb sc(zeroM M).
Proof. intros entry count phi HE HP. exfalso. exact(context_empty M sb sc entry HE). Qed.

Lemma source_full_piece_truth M b c l k truth:
  context_bounded M b c l k ->sf_relation M SFImpl(zeroM M)(zeroM M)truth ->source_full_prv M b c l truth.
Proof.
  intros HC HT. destruct(environment_cons_total M b c l(zeroM M)) as(ub&uc&un&HCons).
  assert(HNew:context_bounded M ub uc un k).
  { exact(proj2(context_bounded_cons M b c l(zeroM M)ub uc un k HCons)(conj(source_bounded_accept_falsity M k)HC)). }
  apply(full_source_II M b c l(zeroM M)(zeroM M)truth ub uc un);[| |exact HCons|exact HT].
  - exists k. split;[|exact HC]. exact(proj2(source_bounded_accept_binary M SFImpl(zeroM M)(zeroM M)truth k
      (or_intror(or_intror eq_refl))HT)(conj(source_bounded_accept_falsity M k)(source_bounded_accept_falsity M k))).
  - apply full_source_Ctx;[exists k;auto using source_bounded_accept_falsity|].
    apply(proj2(context_member_cons M b c l(zeroM M)ub uc un(zeroM M)HCons)). now left.
Qed.

Theorem source_zfr_pcf_bound_zero M domain level sb sc g X ordinal goal implication k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  coding_lt M g k ->coding_lt M X k ->numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_pcf_bound_goal M domain level sb sc(zeroM M)g X goal ->sf_relation M SFImpl ordinal goal implication ->
  source_zfr_provable M implication.
Proof.
  intros HD HL HG HX HOrdinal HGoal HImp.
  pose proof(source_piece_table_valid_zero M sb sc) as HV.
  pose proof(source_pcf_bound_goal_bounded M domain level sb sc(zeroM M)g X goal k HD HL HV HG HX HGoal) as BGoal.
  destruct(source_zfr_successor_container_total M g) as(oldOrd&container&body&member&law&HOldOrd&HLaw&HEx&HBody&HMember&PLaw).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)g oldOrd ordinal HOldOrd HOrdinal) as E. subst oldOrd.
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(shifted&HShift).
  pose proof(source_pcf_bound_goal_shift M domain level sb sc(zeroM M)g X goal shifted HD HL HV HGoal HShift) as HShiftGoal.
  destruct(sf_relation_total M SFImpl body shifted) as(witnessImp&HWitness).
  assert(BMember:source_bounded M member(succM M k)).
  { exact(proj2(source_bounded_accept_atom M SFMember(succM M g)(zeroM M)member(succM M k)
      (or_introl eq_refl)HMember)(conj(proj2(coding_lt_succ_cancel M g k)HG)(coding_zero_lt_succ M k))). }
  assert(BBody:source_bounded M body(succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFAnd(source_ordinal_predicate_code M)member body(succM M k)
      (or_introl eq_refl)HBody)(conj(sr_domain_bound_succ M(source_ordinal_predicate_code M)k
        (source_ordinal_predicate_bounded M))BMember)). }
  pose proof(source_pcf_bound_goal_bounded M domain level sb sc(zeroM M)(succM M g)(succM M X)shifted(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)HShiftGoal) as BShifted.
  assert(PWitness:source_zfr_provable M witnessImp).
  { apply(proj1(source_zfr_descriptor_provable M witnessImp)).
    apply(source_descriptor_provable_from_empty M ZFRSourceDescriptor witnessImp).
    destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)body) as(b&c&l&HCons).
    pose proof(proj2(context_bounded_cons M(zeroM M)(zeroM M)(zeroM M)body b c l(succM M k)HCons)
      (conj BBody(context_bounded_empty M(zeroM M)(zeroM M)(succM M k)))) as HC.
    assert(PBody:source_full_prv M b c l body).
    { apply full_source_Ctx;[exists(succM M k);auto|].
      apply(proj2(context_member_cons M(zeroM M)(zeroM M)(zeroM M)body b c l body HCons)). now left. }
    destruct(source_full_piece_conjunction_components M b c l(source_ordinal_predicate_code M)member body HBody PBody) as[PO PM].
    destruct(source_piece_conjunction_total M domain level sb sc(zeroM M)(zeroM M)(succM M X)) as(pc&HPC).
    pose proof(proj1(source_piece_conjunction_zero M domain level sb sc(zeroM M)(succM M X)pc)HPC) as HTruth.
    pose proof(source_full_piece_truth M b c l(succM M k)pc HC HTruth) as PPc.
    pose proof(source_full_pcf_bound_intro M b c l domain level sb sc(zeroM M)(succM M g)(succM M X)shifted
      (zeroM M)(source_ordinal_predicate_code M)member pc(succM M k)HD HL HV
      (proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)(coding_zero_lt_succ M k)
      HC HShiftGoal(source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))
      HMember HPC PO PM PPc) as PShifted.
    apply(full_source_II M(zeroM M)(zeroM M)(zeroM M)body shifted witnessImp b c l);[|exact PShifted|exact HCons|exact HWitness].
    exists(succM M k). split;[|apply context_bounded_empty].
    exact(proj2(source_bounded_accept_binary M SFImpl body shifted witnessImp(succM M k)
      (or_intror(or_intror eq_refl))HWitness)(conj BBody BShifted)). }
  assert(BContainer:source_bounded M container k).
  { exact(proj2(source_bounded_accept_unary M SFEx body container k(or_intror eq_refl)HEx)BBody). }
  destruct(sf_relation_total M SFImpl container goal) as(exImp&HExImp).
  pose proof(source_zfr_exists_implication M body container goal shifted witnessImp exImp k k
    BContainer BGoal HEx HShift HWitness HExImp PWitness) as PExImp.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal k
    (source_ordinal_predicate_bounded M)HG HOrdinal) as BOrdinal.
  assert(HEnv:forall i,source_bounded M(source_cb_four_environment ordinal container goal goal i)k).
  { intros[|[|[|i]]];cbn[source_cb_four_environment];assumption. }
  apply(source_zfr_prop_two M source_cb_ord_total_template source_cb_total_goal_template source_cb_ord_goal_template
    source_cb_compose_total_program(source_cb_four_environment ordinal container goal goal)k law exImp implication HEnv);
    assumption.
Qed.

Print Assumptions source_full_piece_truth.
Print Assumptions source_zfr_pcf_bound_zero.
