(** Both predecessor existential eliminations in attempt agreement. The
    needed arbitrary-matrix equality certificate is generated internally. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull SourceTraceBounds SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAgreement SourceRecursionFunctionality SourceRecursionFunctionalityClosed
 SourceRecursionAttemptStepShell SourceRecursionShiftGraphs SourceRecursionValuePairs SourceRecursionAgreementPoints
 SourceRecursionBinaryInstance SourceProofRenaming SourceImplicationAllShift SourceClosedContextShift SourceContextTransport
 SourceContextProofHelpers SourceProofWeakening SourceLeastOrdinalWitness SourcePieceBoundMaxJoint SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_rec_witness_agreement M phi funlaw f g z v w agr exF exG equal t3 t2 t1 law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M f k ->coding_lt M g k ->coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->
 source_rec_functionality M phi funlaw ->source_rec_agreement M f g z agr ->
 source_rec_transition_witness M phi f z v exF ->source_rec_transition_witness M phi g z w exG ->sf_relation M SFEqual v w equal ->
 sf_relation M SFImpl exG equal t3 ->sf_relation M SFImpl exF t3 t2 ->sf_relation M SFImpl agr t2 t1 ->sf_relation M SFImpl funlaw t1 law ->
 source_zfr_provable M law.
Proof.
 intros BP BF BG BZ BV BW HFun HA HEF HEG HE H3 H2 H1 HL.
 pose proof(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k))as BFun.
 pose proof(source_rec_agreement_bounded M f g z agr k BF BG BZ HA)as BAgr.
 pose proof(source_rec_transition_witness_bounded M phi f z v exF k BP BF BZ BV HEF)as BEF.
 pose proof(source_rec_transition_witness_bounded M phi g z w exG k BP BG BZ BW HEG)as BEG.
 pose proof(proj2(source_bounded_accept_atom M SFEqual v w equal k(or_intror eq_refl)HE)(conj BV BW))as BE.
 pose proof(proj2(source_bounded_accept_binary M SFImpl exG equal t3 k(or_intror(or_intror eq_refl))H3)(conj BEG BE))as B3.
 pose proof(proj2(source_bounded_accept_binary M SFImpl exF t3 t2 k(or_intror(or_intror eq_refl))H2)(conj BEF B3))as B2.
 pose proof(proj2(source_bounded_accept_binary M SFImpl agr t2 t1 k(or_intror(or_intror eq_refl))H1)(conj BAgr B2))as B1.
 pose proof(proj2(source_bounded_accept_binary M SFImpl funlaw t1 law k(or_intror(or_intror eq_refl))HL)(conj BFun B1))as BLaw.
 pose proof HEF as HEFCopy. destruct HEFCopy as(appF1&binaryF1&bodyF1&HAppF1&HBinaryF1&HBodyF1&HExF).
 destruct(source_rec_transition_witness_total M phi(succM M g)(succM M z)(succM M w))as(exG1&HEG1).
 pose proof HEG1 as HEG1Copy. destruct HEG1Copy as(appG2&binaryG2&bodyG2&HAppG2&HBinaryG2&HBodyG2&HExG1).
 pose proof(source_rec_transition_witness_shift M phi g z w exG exG1 BP HEG HEG1)as SExG.
 destruct(source_rec_agreement_total M(succM M f)(succM M g)(succM M z))as(agr1&HA1).
 destruct(source_rec_agreement_total M(succM M(succM M f))(succM M(succM M g))(succM M(succM M z)))as(agr2&HA2).
 pose proof(source_rec_agreement_shift M f g z agr agr1 HA HA1)as SA1.
 pose proof(source_rec_agreement_shift M(succM M f)(succM M g)(succM M z)agr1 agr2 HA1 HA2)as SA2.
 destruct(source_rec_value_pair_total M phi(succM M(succM M f))(succM M(succM M z))(code_numeral M 1)(succM M(succM M v)))as(bodyF2&HValueF2).
 pose proof HValueF2 as HValueF2Copy. destruct HValueF2Copy as(appF2&binaryF2&HAppF2&HBinaryF2&HBodyF2).
 assert(HValueF1:source_rec_value_pair M phi(succM M f)(succM M z)(zeroM M)(succM M v)bodyF1).
 { exists appF1,binaryF1. auto. }
 pose proof(source_rec_value_pair_shift M phi(succM M f)(succM M z)(zeroM M)(succM M v)bodyF1 bodyF2 BP HValueF1 HValueF2)as SBodyF.
 destruct(sf_relation_total M SFEqual(succM M v)(succM M w))as(equal1&HE1).
 destruct(sf_relation_total M SFEqual(succM M(succM M v))(succM M(succM M w)))as(equal2&HE2).
 assert(SE1:source_formula_shift M equal equal1).
 { apply(proj2(numerical_renaming_equal M v w equal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)equal1 HE)).
   exists(succM M v),(succM M w). repeat split;try assumption;apply context_shift_lookup;reflexivity. }
 assert(SE2:source_formula_shift M equal1 equal2).
 { apply(proj2(numerical_renaming_equal M(succM M v)(succM M w)equal1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)equal2 HE1)).
   exists(succM M(succM M v)),(succM M(succM M w)). repeat split;try assumption;apply context_shift_lookup;reflexivity. }
 destruct(source_rec_binary_total M phi(code_numeral M 1)(succM M(succM M w)))as(moved&HMoved).
 destruct(sf_relation_total M SFEqual(code_numeral M 1)(zeroM M))as(inputsEqual&HInputsEqual).
 destruct(sf_relation_total M SFImpl binaryG2 moved)as(movePoint&HMovePoint).
 destruct(sf_relation_total M SFImpl inputsEqual movePoint)as(moveLaw&HMoveLaw).
 pose proof(source_zfr_rec_agreement_transport M phi(code_numeral M 1)(zeroM M)(succM M(succM M w))binaryG2 moved inputsEqual movePoint moveLaw(succM M(succM M k))
  BP(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))(coding_zero_lt_succ M k))(coding_zero_lt_succ M(succM M k))
  (proj2(coding_lt_succ_cancel M(succM M w)(succM M k))(proj2(coding_lt_succ_cancel M w k)BW))HMoved HBinaryG2 HInputsEqual HMovePoint HMoveLaw)as PMove.
 destruct PMove as(cb&cc&cn&HClosed&PMove).
 pose proof(source_zfr_context_closed M cb cc cn HClosed)as CClosed.
 pose proof(context_bounded_monotone M cb cc cn(zeroM M)k CClosed(coding_zero_lt_succ M k))as C0.
 destruct(environment_cons_total M cb cc cn funlaw)as(b1&c1&n1&HC1).
 pose proof(proj2(context_bounded_cons M cb cc cn funlaw b1 c1 n1 k HC1)(conj BFun C0))as C1.
 destruct(environment_cons_total M b1 c1 n1 agr)as(b2&c2&n2&HC2).
 pose proof(proj2(context_bounded_cons M b1 c1 n1 agr b2 c2 n2 k HC2)(conj BAgr C1))as C2.
 destruct(environment_cons_total M b2 c2 n2 exF)as(b3&c3&n3&HC3).
 pose proof(proj2(context_bounded_cons M b2 c2 n2 exF b3 c3 n3 k HC3)(conj BEF C2))as C3.
 destruct(environment_cons_total M b3 c3 n3 exG)as(b4&c4&n4&HC4).
 pose proof(proj2(context_bounded_cons M b3 c3 n3 exG b4 c4 n4 k HC4)(conj BEG C3))as C4.
 assert(Background:context_included M cb cc cn b4 c4 n4).
 { intros ax HAx.
   apply(source_cons_tail_inclusion M b3 c3 n3 exG b4 c4 n4 HC4).
   apply(source_cons_tail_inclusion M b2 c2 n2 exF b3 c3 n3 HC3).
   apply(source_cons_tail_inclusion M b1 c1 n1 agr b2 c2 n2 HC2).
   apply(source_cons_tail_inclusion M cb cc cn funlaw b1 c1 n1 HC1).
   exact HAx. }
 assert(P1:source_full_prv M b4 c4 n4 funlaw).
 { apply full_source_Ctx;[exists k;exact(conj BFun C4)|].
   apply(source_cons_tail_inclusion M b3 c3 n3 exG b4 c4 n4 HC4).
   apply(source_cons_tail_inclusion M b2 c2 n2 exF b3 c3 n3 HC3).
   apply(source_cons_tail_inclusion M b1 c1 n1 agr b2 c2 n2 HC2).
   apply(proj2(context_member_cons M cb cc cn funlaw b1 c1 n1 funlaw HC1)). now left. }
 assert(P2:source_full_prv M b4 c4 n4 agr).
 { apply full_source_Ctx;[exists k;exact(conj BAgr C4)|].
   apply(source_cons_tail_inclusion M b3 c3 n3 exG b4 c4 n4 HC4).
   apply(source_cons_tail_inclusion M b2 c2 n2 exF b3 c3 n3 HC3).
   apply(proj2(context_member_cons M b1 c1 n1 agr b2 c2 n2 agr HC2)). now left. }
 assert(P3:source_full_prv M b4 c4 n4 exF).
 { apply full_source_Ctx;[exists k;exact(conj BEF C4)|].
   apply(source_cons_tail_inclusion M b3 c3 n3 exG b4 c4 n4 HC4).
   apply(proj2(context_member_cons M b2 c2 n2 exF b3 c3 n3 exF HC3)). now left. }
 assert(P4:source_full_prv M b4 c4 n4 exG).
 { apply full_source_Ctx;[exists k;exact(conj BEG C4)|].
   apply(proj2(context_member_cons M b3 c3 n3 exG b4 c4 n4 exG HC4)). now left. }
 destruct(context_shift_total M b4 c4 n4)as(sb&sc&HS).
 pose proof(context_shift_preserves_bound M b4 c4 n4 sb sc k HS C4)as CS.
 pose proof(proj1(source_bounded_accept_unary M SFEx bodyF1 exF k(or_intror eq_refl)HExF)BEF)as BBodyF1.
 destruct(environment_cons_total M sb sc n4 bodyF1)as(b5&c5&n5&HC5).
 pose proof(proj2(context_bounded_cons M sb sc n4 bodyF1 b5 c5 n5(succM M k)HC5)(conj BBodyF1 CS))as C5.
 pose proof(source_rec_functionality_shift M phi funlaw BP HFun)as SFun.
 pose proof(source_full_cons_weaken M sb sc n4 bodyF1 b5 c5 n5(succM M k)funlaw HC5 C5
  (source_full_prv_renaming M b4 c4 n4 funlaw(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc funlaw P1 HS SFun))as PFun1.
 pose proof(source_full_cons_weaken M sb sc n4 bodyF1 b5 c5 n5(succM M k)agr1 HC5 C5
  (source_full_prv_renaming M b4 c4 n4 agr(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc agr1 P2 HS SA1))as PAgr1.
 pose proof(source_full_cons_weaken M sb sc n4 bodyF1 b5 c5 n5(succM M k)exG1 HC5 C5
  (source_full_prv_renaming M b4 c4 n4 exG(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc exG1 P4 HS SExG))as PExG1.
 pose proof(source_full_cons_head M sb sc n4 bodyF1 b5 c5 n5(succM M k)HC5 BBodyF1 C5)as PBodyF1.
 destruct(context_shift_total M b5 c5 n5)as(tb&tc&HT).
 pose proof(context_shift_preserves_bound M b5 c5 n5 tb tc(succM M k)HT C5)as CT.
 pose proof(source_shift_bound M exG exG1 k BEG SExG)as BEG1.
 pose proof(proj1(source_bounded_accept_unary M SFEx bodyG2 exG1(succM M k)(or_intror eq_refl)HExG1)BEG1)as BBodyG2.
 destruct(environment_cons_total M tb tc n5 bodyG2)as(b6&c6&n6&HC6).
 pose proof(proj2(context_bounded_cons M tb tc n5 bodyG2 b6 c6 n6(succM M(succM M k))HC6)(conj BBodyG2 CT))as C6.
 pose proof(source_full_cons_weaken M tb tc n5 bodyG2 b6 c6 n6(succM M(succM M k))funlaw HC6 C6
  (source_full_prv_renaming M b5 c5 n5 funlaw(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)tb tc funlaw PFun1 HT SFun))as PFun2.
 pose proof(source_full_cons_weaken M tb tc n5 bodyG2 b6 c6 n6(succM M(succM M k))agr2 HC6 C6
  (source_full_prv_renaming M b5 c5 n5 agr1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)tb tc agr2 PAgr1 HT SA2))as PAgr2.
 pose proof(source_full_cons_weaken M tb tc n5 bodyG2 b6 c6 n6(succM M(succM M k))bodyF2 HC6 C6
  (source_full_prv_renaming M b5 c5 n5 bodyF1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)tb tc bodyF2 PBodyF1 HT SBodyF))as PBodyF2.
 pose proof(source_full_cons_head M tb tc n5 bodyG2 b6 c6 n6(succM M(succM M k))HC6 BBodyG2 C6)as PBodyG2.
 assert(BackgroundS:context_included M cb cc cn sb sc n4).
 { exact(source_context_included_shift M cb cc cn b4 c4 n4 cb cc sb sc Background(source_closed_context_shift_self M cb cc cn CClosed)HS). }
 assert(Background5:context_included M cb cc cn b5 c5 n5).
 { intros ax HAx. apply(source_cons_tail_inclusion M sb sc n4 bodyF1 b5 c5 n5 HC5). exact(BackgroundS ax HAx). }
 assert(BackgroundT:context_included M cb cc cn tb tc n5).
 { exact(source_context_included_shift M cb cc cn b5 c5 n5 cb cc tb tc Background5(source_closed_context_shift_self M cb cc cn CClosed)HT). }
 assert(Background6:context_included M cb cc cn b6 c6 n6).
 { intros ax HAx. apply(source_cons_tail_inclusion M tb tc n5 bodyG2 b6 c6 n6 HC6). exact(BackgroundT ax HAx). }
 pose proof(source_full_prv_weaken_bounded M cb cc cn b6 c6 n6 moveLaw(succM M(succM M k))PMove Background6 C6)as PMove6.
 destruct(source_full_piece_conjunction_components M b6 c6 n6 appF2 binaryF2 bodyF2 HBodyF2 PBodyF2)as[PAppF2 PBinaryF2].
 destruct(source_full_piece_conjunction_components M b6 c6 n6 appG2 binaryG2 bodyG2 HBodyG2 PBodyG2)as[PAppG2 PBinaryG2].
 pose proof(source_full_rec_agreement_predecessors M b6 c6 n6 phi funlaw(succM M(succM M f))(succM M(succM M g))(succM M(succM M z))agr2
  (code_numeral M 1)(zeroM M)(succM M(succM M v))(succM M(succM M w))appF2 appG2 binaryF2 binaryG2 moved inputsEqual equal2 movePoint moveLaw
  BP HFun HA2 HAppF2 HAppG2 HBinaryF2 HBinaryG2 HMoved HInputsEqual HE2 HMovePoint HMoveLaw PFun2 PAgr2 PAppF2 PAppG2 PBinaryF2 PBinaryG2 PMove6)as PEqual2.
 pose proof(source_shift_bound M equal equal1 k BE SE1)as BE1.
 pose proof(full_source_ExE M b5 c5 n5 bodyG2 exG1 equal1 equal2 tb tc b6 c6 n6(ex_intro _ (succM M k)(conj BE1 C5))PExG1 PEqual2 HExG1 HT HC6 SE2)as PEqual1.
 pose proof(full_source_ExE M b4 c4 n4 bodyF1 exF equal equal1 sb sc b5 c5 n5(ex_intro _ k(conj BE C4))P3 PEqual1 HExF HS HC5 SE1)as PEqual.
 pose proof(full_source_II M b3 c3 n3 exG equal t3 b4 c4 n4(ex_intro _ k(conj B3 C3))PEqual HC4 H3)as PT3.
 pose proof(full_source_II M b2 c2 n2 exF t3 t2 b3 c3 n3(ex_intro _ k(conj B2 C2))PT3 HC3 H2)as PT2.
 pose proof(full_source_II M b1 c1 n1 agr t2 t1 b2 c2 n2(ex_intro _ k(conj B1 C1))PT2 HC2 H1)as PT1.
 exists cb,cc,cn. split;[exact HClosed|].
 exact(full_source_II M cb cc cn funlaw t1 law b1 c1 n1(ex_intro _ k(conj BLaw C0))PT1 HC1 HL).
Qed.
Print Assumptions source_zfr_rec_witness_agreement.
