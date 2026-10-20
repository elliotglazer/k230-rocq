(** The maximum-witness proof is driven by the three literal existential
    witness bodies, without caller-supplied intermediate leaf formulas. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded Pairing NumericalInstantiation
  SourceDomainInstances SourceOrdinalPredicate SourceRawSubset SourceRawSubsetBounds SourceHierarchySyntax
  SourcePieceClosure SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundBody SourcePieceExistentialBody
  SourcePieceBoundMaxJoint SourceZFRProvability.
Unset Implicit Arguments.

Definition source_pcf_max_body M a b d body:=exists ordinal sa sb left,
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal /\source_raw_subset_graph M a d sa /\
  source_raw_subset_graph M b d sb /\sf_relation M SFAnd ordinal sa left /\sf_relation M SFAnd left sb body.

Theorem source_pcf_max_body_bounded M a b d body k:
  coding_lt M a k ->coding_lt M b k ->coding_lt M d k ->source_pcf_max_body M a b d body ->source_bounded M body k.
Proof.
  intros HA HB HD(ordinal&sa&sb&left&HO&HSA&HSB&HL&HBody).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k(source_ordinal_predicate_bounded M)HD HO) as BO.
  pose proof(source_raw_subset_bounded M a d sa k HA HD HSA) as BSA.
  pose proof(source_raw_subset_bounded M b d sb k HB HD HSB) as BSB.
  pose proof(proj2(source_bounded_accept_binary M SFAnd ordinal sa left k(or_introl eq_refl)HL)(conj BO BSA)) as BL.
  exact(proj2(source_bounded_accept_binary M SFAnd left sb body k(or_introl eq_refl)HBody)(conj BL BSB)).
Qed.

Theorem source_zfr_pcf_bound_max_case M domain level sb sc n count phi entry g X goal d1 d2 d
    previous piece maximum pair joint implication k:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_piece_table_valid M sb sc(succM M n) ->coding_lt M g k ->coding_lt M X k ->
  coding_lt M d1 k ->coding_lt M d2 k ->coding_lt M d k ->
  source_pcf_bound_goal M domain level sb sc(succM M n)g X goal ->beta M sb sc n entry ->pair_graph M count phi entry ->
  source_pcf_bound_body M domain level sb sc n g X d1 previous ->
  source_piece_existential_body M domain level count phi d2 X piece ->source_pcf_max_body M d1 d2 d maximum ->
  sf_relation M SFAnd previous piece pair ->sf_relation M SFAnd pair maximum joint ->sf_relation M SFImpl joint goal implication ->
  source_zfr_provable M implication.
Proof.
  intros HD HL HV HG HX HD1 HD2 HDk HGoal HE HP
    (od1&member&prev&prevLeft&HOD1&HM&HPrev&HPL&HPB)(od2&pc&HOD2&HPC&HCB)
    (od&sub1&sub2&maxLeft&HOD&HS1&HS2&HML&HMB)HPair HJoint HImp.
  apply(source_zfr_pcf_bound_max_joint M domain level sb sc n count phi entry g X goal d1 d2 d
    od1 od2 od sub1 sub2 member prev pc joint implication k
    HD HL HV HG HX HD1 HD2 HDk HGoal HE HP HOD1 HOD2 HOD HS1 HS2 HM HPrev HPC);[|exact HImp].
  exists prevLeft,previous,piece,maxLeft,maximum,pair. auto 10.
Qed.

Print Assumptions source_pcf_max_body_bounded.
Print Assumptions source_zfr_pcf_bound_max_case.
