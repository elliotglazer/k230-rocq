(** Actual source reasoning in the maximum-ordinal witness branch of the
    PCf bound construction. Law premises are ordinary numerical source proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded Pairing NumericalContexts NumericalSourceFull
  NumericalInstantiation SourceDerivedRules SourceDomainInstances SourceOrdinalPredicate SourceRawSubset SourceThreeConditions
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundIntroduction.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_full_piece_curried_apply M b c l a h j d e law:
  source_three_curried M a h j d e law ->source_full_prv M b c l law ->
  source_full_prv M b c l a ->source_full_prv M b c l h ->source_full_prv M b c l j ->
  source_full_prv M b c l d ->source_full_prv M b c l e.
Proof.
  intros(de&jde&hjde&HDE&HJD&HHJ&HLaw)PL PA PH PJ PD.
  exact(source_full_modus_ponens M b c l d e de HDE
    (source_full_modus_ponens M b c l j de jde HJD
      (source_full_modus_ponens M b c l h jde hjde HHJ
        (source_full_modus_ponens M b c l a hjde law HLaw PL PA)PH)PJ)PD).
Qed.

Theorem source_full_pcf_bound_max_point M b c l domain level sb sc n count phi entry g X goal
    d1 d2 d od1 od2 od sub1 sub2 memberOld memberNew prevOld prevNew pieceOld pieceNew prefixLaw pieceLaw k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc(succM M n) ->coding_lt M g k ->coding_lt M X k ->
  coding_lt M d1 k ->coding_lt M d2 k ->coding_lt M d k ->context_bounded M b c l k ->
  source_pcf_bound_goal M domain level sb sc(succM M n)g X goal ->
  beta M sb sc n entry ->pair_graph M count phi entry ->
  numerical_instantiation M(source_ordinal_predicate_code M)d1 od1 ->
  numerical_instantiation M(source_ordinal_predicate_code M)d2 od2 ->
  numerical_instantiation M(source_ordinal_predicate_code M)d od ->
  source_raw_subset_graph M d1 d sub1 ->source_raw_subset_graph M d2 d sub2 ->
  sf_relation M SFMember g d1 memberOld ->sf_relation M SFMember g d memberNew ->
  source_piece_conjunction M domain level sb sc n d1 X prevOld ->
  source_piece_conjunction M domain level sb sc n d X prevNew ->
  source_pc_instance M domain level count phi d2 X pieceOld ->source_pc_instance M domain level count phi d X pieceNew ->
  source_three_curried M od1 od sub1 prevOld prevNew prefixLaw ->
  source_three_curried M od2 od sub2 pieceOld pieceNew pieceLaw ->
  source_full_prv M b c l od1 ->source_full_prv M b c l od2 ->source_full_prv M b c l od ->
  source_full_prv M b c l sub1 ->source_full_prv M b c l sub2 ->source_full_prv M b c l memberOld ->
  source_full_prv M b c l prevOld ->source_full_prv M b c l pieceOld ->
  source_full_prv M b c l prefixLaw ->source_full_prv M b c l pieceLaw ->source_full_prv M b c l goal.
Proof.
  intros HD HL HV HG HX HD1 HD2 HDk HC HGoal HE HP HOD1 HOD2 HOD HS1 HS2 HMO HMN
    HPrevOld HPrevNew HPieceOld HPieceNew HPrefixLaw HPieceLaw POD1 POD2 POD PS1 PS2 PMO PPrev PPiece PPL PCL.
  pose proof(source_full_piece_curried_apply M b c l od1 od sub1 prevOld prevNew prefixLaw
    HPrefixLaw PPL POD1 POD PS1 PPrev) as PPrevNew.
  pose proof(source_full_piece_curried_apply M b c l od2 od sub2 pieceOld pieceNew pieceLaw
    HPieceLaw PCL POD2 POD PS2 PPiece) as PPieceNew.
  pose proof(source_full_raw_subset_member M b c l d1 d g sub1 memberOld memberNew HS1 HMO HMN PS1 PMO) as PMN.
  destruct(sf_relation_total M SFAnd prevNew pieceNew) as(joined&HAnd).
  assert(HJoined:source_piece_conjunction M domain level sb sc(succM M n)d X joined).
  { apply source_piece_conjunction_succ. exists prevNew,entry,count,phi,pieceNew. auto 10. }
  pose proof(source_piece_conjunction_bounded M(succM M n)domain level sb sc d X joined k HD HL HV HDk HX HJoined) as BJoined.
  pose proof(full_source_CI M b c l prevNew pieceNew joined(ex_intro _ k(conj BJoined HC))PPrevNew PPieceNew HAnd) as PJoined.
  exact(source_full_pcf_bound_intro M b c l domain level sb sc(succM M n)g X goal d od memberNew joined k
    HD HL HV HG HX HDk HC HGoal HOD HMN HJoined POD PMN PJoined).
Qed.

Print Assumptions source_full_piece_curried_apply.
Print Assumptions source_full_pcf_bound_max_point.
