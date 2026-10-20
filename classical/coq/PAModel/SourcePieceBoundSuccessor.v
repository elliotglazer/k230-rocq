(** The last existential elimination in PCf-bound induction. The induction
    hypothesis is an actual prefix-bound derivation, rather than a semantic
    or proof-transformation assumption. *)
From PAModel Require Import Model FiniteCoding FiniteCRT Pairing CodeExpressions SetFormulaCodes SourceBounded
  SourceDomainInstances SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax SourceRelativizationBounds
  NumericalRenaming NumericalInstantiation SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundRenaming
  SourcePieceBoundBody SourcePieceBoundBodyBounds SourcePieceBoundOneWitness SourceWitnessProofComposition
  SourceCBSuccessor SourcePropositionalTemplates SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_zfr_pcf_bound_successor M level sb sc n count phi entry g X ordinal previous goal oldImp implication k:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc(succM M n) ->
  coding_lt M g k ->coding_lt M X k ->numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_pcf_bound_goal M(source_L_domain_code M)level sb sc n g X previous ->
  source_pcf_bound_goal M(source_L_domain_code M)level sb sc(succM M n)g X goal ->
  beta M sb sc n entry ->pair_graph M count phi entry ->
  sf_relation M SFImpl ordinal previous oldImp ->sf_relation M SFImpl ordinal goal implication ->
  source_zfr_provable M oldImp ->source_zfr_provable M implication.
Proof.
  intros HLevel HV HG HX HOrdinal HPrevious HGoal HE HP HOldImp HImp POld.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
  pose proof(source_pcf_bound_goal_bounded M(source_L_domain_code M)level sb sc n g X previous k HD HL HPrefix HG HX HPrevious) as BPrevious.
  pose proof(source_pcf_bound_goal_bounded M(source_L_domain_code M)level sb sc(succM M n)g X goal k HD HL HV HG HX HGoal) as BGoal.
  destruct(proj1(source_pcf_bound_goal_body M(source_L_domain_code M)level sb sc n g X previous)HPrevious) as(body&HBody&HEx).
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal'&HSGoal).
  pose proof(source_pcf_bound_goal_shift M(source_L_domain_code M)level sb sc(succM M n)g X goal goal' HD HL HV HGoal HSGoal) as HGoal'.
  destruct(sf_relation_total M SFImpl body goal') as(witnessImp&HWitness).
  pose proof(source_zfr_pcf_bound_one_witness M level sb sc n count phi entry(succM M g)(succM M X)goal'
    (zeroM M)body witnessImp(succM M k)HLevel HV(proj2(coding_lt_succ_cancel M g k)HG)
    (proj2(coding_lt_succ_cancel M X k)HX)(coding_zero_lt_succ M k)HGoal' HE HP HBody HWitness) as PWitness.
  destruct(sf_relation_total M SFImpl previous goal) as(use&HUse).
  pose proof(source_zfr_exists_implication M body previous goal goal' witnessImp use k k
    BPrevious BGoal HEx HSGoal HWitness HUse PWitness) as PUse.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal k(source_ordinal_predicate_bounded M)HG HOrdinal) as BOrdinal.
  assert(HEnv:forall i,source_bounded M(source_cb_four_environment ordinal previous goal goal i)k).
  { intros[|[|[|i]]];cbn[source_cb_four_environment];assumption. }
  apply(source_zfr_prop_two M source_cb_ord_total_template source_cb_total_goal_template source_cb_ord_goal_template
    source_cb_compose_total_program(source_cb_four_environment ordinal previous goal goal)k oldImp use implication HEnv);assumption.
Qed.

Print Assumptions source_zfr_pcf_bound_successor.
