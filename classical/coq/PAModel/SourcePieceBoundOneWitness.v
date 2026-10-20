(** Eliminate the last-piece ordinal witness. The prefix witness body is
    retained as the single ordinary antecedent. *)
From PAModel Require Import Model FiniteCoding FiniteCRT Pairing CodeExpressions SetFormulaCodes SourceBounded
  SourceDomainInstances SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax SourceRelativizationBounds SourceQuantifierRules
  NumericalContexts NumericalRenaming NumericalInstantiation NumericalContextRenaming
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundRenaming
  SourcePieceBoundBody SourcePieceBoundBodyBounds SourcePieceExistentialBody SourcePieceBound SourcePieceBoundTwoWitnesses
  SourceWitnessProofComposition SourcePieceBoundPropPrograms SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_pcf_exchange_program :source_prop_program
  [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))]
  (SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2))).
Proof.
  apply SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE;apply SPTCtx;[right;right;now left|now left].
  - apply SPTCtx. right;now left.
Qed.

Theorem source_zfr_pcf_bound_one_witness M level sb sc n count phi entry g X goal d previous target k:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc(succM M n) ->
  coding_lt M g k ->coding_lt M X k ->coding_lt M d k ->
  source_pcf_bound_goal M(source_L_domain_code M)level sb sc(succM M n)g X goal ->
  beta M sb sc n entry ->pair_graph M count phi entry ->
  source_pcf_bound_body M(source_L_domain_code M)level sb sc n g X d previous ->
  sf_relation M SFImpl previous goal target ->source_zfr_provable M target.
Proof.
  intros HLevel HV HG HX HDk HGoal HE HP HPrevious HTarget.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
  assert(HEntry:context_member M sb sc(succM M n)entry) by(exists n;split;[apply coding_lt_succ|exact HE]).
  pose proof(HV entry count phi HEntry HP) as HB.
  pose proof(source_pcf_bound_body_bounded M(source_L_domain_code M)level sb sc n g X d previous k HD HL HPrefix HG HX HDk HPrevious) as BPrevious.
  pose proof(source_pcf_bound_goal_bounded M(source_L_domain_code M)level sb sc(succM M n)g X goal k HD HL HV HG HX HGoal) as BGoal.
  pose proof(proj2(source_bounded_accept_binary M SFImpl previous goal target k(or_intror(or_intror eq_refl))HTarget)(conj BPrevious BGoal)) as BTarget.
  destruct HPrevious as(ordinal&member&prev&prevLeft&HOrdinal&HMember&HPrev&HLeft&HBody).
  destruct(source_piece_existential_body_total M(source_L_domain_code M)level count phi(zeroM M)(succM M X)) as(piece&HBodyPiece).
  pose proof HBodyPiece as HBodyPieceSave.
  destruct HBodyPiece as(oldOrdinal&pc&HOldOrdinal&HPC&HPiece).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(zeroM M)oldOrdinal(source_ordinal_predicate_code M)
    HOldOrdinal(source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))) as E. subst oldOrdinal.
  destruct(sf_relation_total M SFEx piece(zeroM M)) as(pieceEx&HPieceEx).
  destruct(sf_relation_total M SFImpl ordinal pieceEx) as(pieceLaw&HPieceLaw).
  pose proof(source_zfr_pc_bound M level count phi d X ordinal pc piece pieceEx pieceLaw HLevel HB HOrdinal HPC HPiece HPieceEx HPieceLaw) as PPieceLaw.
  destruct(numerical_renaming_total M previous(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(previous'&HSPrevious).
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal'&HSGoal).
  assert(HPrevious':source_pcf_bound_body M(source_L_domain_code M)level sb sc n(succM M g)(succM M X)(succM M d)previous').
  { apply(source_pcf_bound_body_renaming M(source_L_domain_code M)level sb sc n g X d previous(zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1)(succM M g)(succM M X)(succM M d)previous' HD HL HPrefix).
    - exists ordinal,member,prev,prevLeft. auto.
    - exact HSPrevious.
    - apply context_shift_lookup;reflexivity.
    - apply context_shift_lookup;reflexivity.
    - apply context_shift_lookup;reflexivity. }
  pose proof(source_pcf_bound_goal_shift M(source_L_domain_code M)level sb sc(succM M n)g X goal goal' HD HL HV HGoal HSGoal) as HGoal'.
  destruct(sf_relation_total M SFImpl piece goal') as(inner'&HInner').
  destruct(sf_relation_total M SFImpl previous' inner') as(point& HPoint).
  pose proof(source_zfr_pcf_bound_two_witnesses M(source_L_domain_code M)level sb sc n count phi entry
    (succM M g)(succM M X)goal'(succM M d)(zeroM M)previous' piece inner' point(succM M k)
    HD HLevel HV(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)
    (proj2(coding_lt_succ_cancel M d k)HDk)(coding_zero_lt_succ M k)HGoal' HE HP HPrevious' HBodyPieceSave HInner' HPoint) as PPoint.
  destruct(sf_relation_total M SFImpl previous' goal') as(target'&HTarget').
  destruct(sf_relation_total M SFImpl piece target') as(witnessImp&HWitness).
  pose proof(source_pcf_bound_body_bounded M(source_L_domain_code M)level sb sc n(succM M g)(succM M X)(succM M d)previous'(succM M k)
    HD HL HPrefix(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)
    (proj2(coding_lt_succ_cancel M d k)HDk)HPrevious') as BPrevious'.
  pose proof(source_pcf_bound_goal_bounded M(source_L_domain_code M)level sb sc(succM M n)(succM M g)(succM M X)goal'(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)HGoal') as BGoal'.
  pose proof(source_piece_existential_body_bounded M(source_L_domain_code M)level count phi(zeroM M)(succM M X)piece(succM M k)
    HD HL HB(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M X k)HX)HBodyPieceSave) as BPiece.
  assert(PWitness:source_zfr_provable M witnessImp).
  { apply(source_zfr_prop_one M(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))
      (SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2)))source_pcf_exchange_program
      (source_pcf_four_environment previous' piece goal' goal')(succM M k)point witnessImp).
    - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
    - unfold source_prop_expression. functionality_graph.
    - unfold source_prop_expression. functionality_graph.
    - exact PPoint. }
  pose proof(source_implication_shift_graph M previous goal target previous' goal' target' HTarget HTarget' HSPrevious HSGoal) as HSTarget.
  pose proof(proj2(source_bounded_accept_unary M SFEx piece pieceEx k(or_intror eq_refl)HPieceEx)BPiece) as BPieceEx.
  destruct(sf_relation_total M SFImpl pieceEx target) as(use&HUse).
  pose proof(source_zfr_exists_implication M piece pieceEx target target' witnessImp use k k
    BPieceEx BTarget HPieceEx HSTarget HWitness HUse PWitness) as PUse.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k(source_ordinal_predicate_bounded M)HDk HOrdinal) as BOrdinal.
  pose proof(proj2(source_bounded_accept_atom M SFMember g d member k(or_introl eq_refl)HMember)(conj HG HDk)) as BMember.
  pose proof(source_piece_conjunction_bounded M n(source_L_domain_code M)level sb sc d X prev k HD HL HPrefix HDk HX HPrev) as BPrev.
  apply(source_zfr_prop_two M pcf_previous_exists pcf_previous_use pcf_previous_output source_pcf_previous_shell_program
    (source_pcf_seven_environment ordinal ordinal member prev pieceEx goal goal)k pieceLaw use target).
  - intros[|[|[|[|[|[|i]]]]]];cbn[source_pcf_seven_environment];assumption.
  - unfold pcf_previous_exists,source_prop_expression. functionality_graph.
  - unfold pcf_previous_use,pcf_successor_A,source_prop_expression. functionality_graph.
  - unfold pcf_previous_output,pcf_successor_A,source_prop_expression. functionality_graph.
  - exact PPieceLaw.
  - exact PUse.
Qed.

Print Assumptions source_pcf_exchange_program.
Print Assumptions source_zfr_pcf_bound_one_witness.
