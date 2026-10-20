(** Eliminate the maximum-ordinal witness in the PCf successor proof.
    The remaining two ordinary assumptions are precisely the prefix and
    last-piece existential witness bodies. *)
From PAModel Require Import Model FiniteCoding FiniteCRT Pairing CodeExpressions SetFormulaCodes SourceBounded
  SourceDomainInstances SourceOrdinalPredicate SourceHierarchySyntax SourceQuantifierRules SourceRelativizationBounds
  NumericalContexts NumericalRenaming NumericalInstantiation NumericalContextRenaming
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundRenaming SourcePieceBoundBody SourcePieceBoundBodyBounds
  SourcePieceExistentialBody SourcePieceBoundMaxCase SourceOrdinalMaxShell SourceRawSubsetBounds
  SourceWitnessProofComposition SourcePieceBoundPropPrograms SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_pcf_seven_environment {A:Type}(a b c d e f g:A)(i:nat):=
  match i with 0=>a|1=>b|2=>c|3=>d|4=>e|5=>f|_=>g end.
Definition source_pcf_four_environment {A:Type}(a b c d:A)(i:nat):=match i with 0=>a|1=>b|2=>c|_=>d end.

Theorem source_zfr_pcf_bound_two_witnesses M domain level sb sc n count phi entry g X goal
    d1 d2 previous piece inner target k:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_piece_table_valid M sb sc(succM M n) ->coding_lt M g k ->coding_lt M X k ->
  coding_lt M d1 k ->coding_lt M d2 k ->
  source_pcf_bound_goal M domain level sb sc(succM M n)g X goal ->beta M sb sc n entry ->pair_graph M count phi entry ->
  source_pcf_bound_body M domain level sb sc n g X d1 previous ->
  source_piece_existential_body M domain level count phi d2 X piece ->
  sf_relation M SFImpl piece goal inner ->sf_relation M SFImpl previous inner target ->source_zfr_provable M target.
Proof.
  intros HD HLevel HV HG HX HD1 HD2 HGoal HE HP HPrevious HPiece HInner HTarget.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
  assert(HEntry:context_member M sb sc(succM M n)entry) by(exists n;split;[apply coding_lt_succ|exact HE]).
  pose proof(HV entry count phi HEntry HP) as HB.
  pose proof(source_pcf_bound_body_bounded M domain level sb sc n g X d1 previous k HD HL HPrefix HG HX HD1 HPrevious) as BPrevious.
  pose proof(source_piece_existential_body_bounded M domain level count phi d2 X piece k HD HL HB HD2 HX HPiece) as BPiece.
  pose proof(source_pcf_bound_goal_bounded M domain level sb sc(succM M n)g X goal k HD HL HV HG HX HGoal) as BGoal.
  pose proof(proj2(source_bounded_accept_binary M SFImpl piece goal inner k(or_intror(or_intror eq_refl))HInner)(conj BPiece BGoal)) as BInner.
  pose proof(proj2(source_bounded_accept_binary M SFImpl previous inner target k(or_intror(or_intror eq_refl))HTarget)(conj BPrevious BInner)) as BTarget.
  destruct HPrevious as(od1&member&prev&prevLeft&HOD1&HM&HPrev&HPL&HPB).
  destruct HPiece as(od2&pc&HOD2&HPC&HCB).
  destruct(source_zfr_ordinal_max_shell M d1 d2) as(old1&old2&sa&sd&maxLeft&maxBody&maxEx&tail&maxLaw&HMax& PMaxLaw).
  destruct HMax as(HOld1&HOld2&HSA&HSD&HML&HMB&HMaxEx&HMaxTail&HMaxLaw).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)d1 old1 od1 HOld1 HOD1) as E. subst old1.
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)d2 old2 od2 HOld2 HOD2) as E. subst old2.
  assert(HMaxBody:source_pcf_max_body M(succM M d1)(succM M d2)(zeroM M)maxBody).
  { exists(source_ordinal_predicate_code M),sa,sd,maxLeft. split;[apply source_domain_instance_zero,source_ordinal_predicate_bounded|]. auto. }
  destruct(numerical_renaming_total M previous(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(previous'&HSPrevious).
  destruct(numerical_renaming_total M piece(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(piece'&HSPiece).
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal'&HSGoal).
  assert(HPrevious':source_pcf_bound_body M domain level sb sc n(succM M g)(succM M X)(succM M d1)previous').
  { apply(source_pcf_bound_body_renaming M domain level sb sc n g X d1 previous(zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1)(succM M g)(succM M X)(succM M d1)previous' HD HL HPrefix).
    - exists od1,member,prev,prevLeft. auto.
    - exact HSPrevious.
    - apply context_shift_lookup;reflexivity.
    - apply context_shift_lookup;reflexivity.
    - apply context_shift_lookup;reflexivity. }
  assert(HPiece':source_piece_existential_body M domain level count phi(succM M d2)(succM M X)piece').
  { apply(source_piece_existential_body_renaming M domain level count phi d2 X piece(zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1)(succM M d2)(succM M X)piece' HD HL HB).
    - exists od2,pc. auto.
    - exact HSPiece.
    - apply context_shift_lookup;reflexivity.
    - apply context_shift_lookup;reflexivity. }
  pose proof(source_pcf_bound_goal_shift M domain level sb sc(succM M n)g X goal goal' HD HL HV HGoal HSGoal) as HGoal'.
  destruct(sf_relation_total M SFAnd previous' piece') as(pair'&HPair').
  destruct(sf_relation_total M SFAnd pair' maxBody) as(joint'&HJoint').
  destruct(sf_relation_total M SFImpl joint' goal') as(pointLaw&HPointLaw).
  pose proof(source_zfr_pcf_bound_max_case M domain level sb sc n count phi entry(succM M g)(succM M X)goal'
    (succM M d1)(succM M d2)(zeroM M)previous' piece' maxBody pair' joint' pointLaw(succM M k)
    HD HLevel HV(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)
    (proj2(coding_lt_succ_cancel M d1 k)HD1)(proj2(coding_lt_succ_cancel M d2 k)HD2)(coding_zero_lt_succ M k)
    HGoal' HE HP HPrevious' HPiece' HMaxBody HPair' HJoint' HPointLaw) as PPoint.
  destruct(sf_relation_total M SFImpl piece' goal') as(inner'&HInner').
  destruct(sf_relation_total M SFImpl previous' inner') as(target'&HTarget').
  destruct(sf_relation_total M SFImpl maxBody target') as(witnessImp&HWitness).
  pose proof(source_pcf_bound_body_bounded M domain level sb sc n(succM M g)(succM M X)(succM M d1)previous'(succM M k)
    HD HL HPrefix(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)
    (proj2(coding_lt_succ_cancel M d1 k)HD1)HPrevious') as BPrevious'.
  pose proof(source_piece_existential_body_bounded M domain level count phi(succM M d2)(succM M X)piece'(succM M k)
    HD HL HB(proj2(coding_lt_succ_cancel M d2 k)HD2)(proj2(coding_lt_succ_cancel M X k)HX)HPiece') as BPiece'.
  pose proof(source_pcf_bound_goal_bounded M domain level sb sc(succM M n)(succM M g)(succM M X)goal'(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M g k)HG)(proj2(coding_lt_succ_cancel M X k)HX)HGoal') as BGoal'.
  pose proof(source_pcf_max_body_bounded M(succM M d1)(succM M d2)(zeroM M)maxBody(succM M k)
    (proj2(coding_lt_succ_cancel M d1 k)HD1)(proj2(coding_lt_succ_cancel M d2 k)HD2)(coding_zero_lt_succ M k)HMaxBody) as BMaxBody.
  assert(PCurry:source_zfr_provable M witnessImp).
  { apply(source_zfr_prop_one M pcf_curry_input pcf_curry_output source_pcf_curry_program
      (source_pcf_four_environment previous' piece' maxBody goal')(succM M k)pointLaw witnessImp).
    - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
    - unfold pcf_curry_input,source_prop_expression. functionality_graph.
    - unfold pcf_curry_output,source_prop_expression. functionality_graph.
    - exact PPoint. }
  pose proof(source_implication_shift_graph M piece goal inner piece' goal' inner' HInner HInner' HSPiece HSGoal) as HSInner.
  pose proof(source_implication_shift_graph M previous inner target previous' inner' target' HTarget HTarget' HSPrevious HSInner) as HSTarget.
  pose proof(proj2(source_bounded_accept_unary M SFEx maxBody maxEx k(or_intror eq_refl)HMaxEx)BMaxBody) as BMaxEx.
  destruct(sf_relation_total M SFImpl maxEx target) as(use&HUse).
  pose proof(source_zfr_exists_implication M maxBody maxEx target target' witnessImp use k k
    BMaxEx BTarget HMaxEx HSTarget HWitness HUse PCurry) as PUse.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d1 od1 k(source_ordinal_predicate_bounded M)HD1 HOD1) as BOD1.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d2 od2 k(source_ordinal_predicate_bounded M)HD2 HOD2) as BOD2.
  pose proof(proj2(source_bounded_accept_atom M SFMember g d1 member k(or_introl eq_refl)HM)(conj HG HD1)) as BMember.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d1 X prev k HD HL HPrefix HD1 HX HPrev) as BPrev.
  pose proof(source_pc_instance_bounded M domain level count phi d2 X pc k HD HL HB HD2 HX HPC) as BPc.
  apply(source_zfr_prop_two M pcf_successor_exists pcf_successor_use pcf_successor_output source_pcf_successor_shell_program
    (source_pcf_seven_environment od1 od2 member prev pc maxEx goal)k maxLaw use target).
  - intros[|[|[|[|[|[|i]]]]]];cbn[source_pcf_seven_environment];assumption.
  - unfold pcf_successor_exists,source_prop_expression. functionality_graph.
  - unfold pcf_successor_use,pcf_successor_A,pcf_successor_B,source_prop_expression. functionality_graph.
  - unfold pcf_successor_output,pcf_successor_A,pcf_successor_B,source_prop_expression. functionality_graph.
  - exact PMaxLaw.
  - exact PUse.
Qed.

Print Assumptions source_zfr_pcf_bound_two_witnesses.
