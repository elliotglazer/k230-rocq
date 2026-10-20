(** Actual ZFR base case of attempt agreement. Both value quantifiers and
    both attempt hypotheses are discharged in the numerical source calculus. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceTraceBounds SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs
 SourceRecursionAgreement SourceRecursionAgreementPoints SourceEqualityForkFacts SourceImplicationAllShift
 SourceZFRProvability SourceClosedContextShift SourceContextProofHelpers SourceProofWeakening SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Theorem source_zfr_rec_agreement_zero M phi o a N f g af ag agr tail result k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->source_rec_agreement M f g o agr ->
 sf_relation M SFImpl ag agr tail ->sf_relation M SFImpl af tail result ->source_zfr_provable M result.
Proof.
 intros BP BO BA BN BF BG HAF HAG HA HT HR.
 pose proof(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF)as BAF.
 pose proof(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG)as BAG.
 pose proof(source_rec_agreement_bounded M f g o agr k BF BG BO HA)as BAgr.
 pose proof(proj2(source_bounded_accept_binary M SFImpl ag agr tail k(or_intror(or_intror eq_refl))HT)(conj BAG BAgr))as BTail.
 pose proof(proj2(source_bounded_accept_binary M SFImpl af tail result k(or_intror(or_intror eq_refl))HR)(conj BAF BTail))as BResult.
 destruct(source_rec_agreement_shell M f g o agr HA)as(left&right&equal&rhs&point&inner&HLeft&HRight&HEqual&HRhs&HPoint&HInner&HOuter).
 pose proof(proj1(source_bounded_accept_unary M SFAll inner agr k(or_introl eq_refl)HOuter)BAgr)as BInner.
 pose proof(proj1(source_bounded_accept_unary M SFAll point inner(succM M k)(or_introl eq_refl)HInner)BInner)as BPoint.
 destruct(proj1(source_bounded_accept_binary M SFImpl left rhs point(succM M(succM M k))(or_intror(or_intror eq_refl))HPoint)BPoint)as[BLeft BRhs].
 destruct(proj1(source_bounded_accept_binary M SFImpl right equal rhs(succM M(succM M k))(or_intror(or_intror eq_refl))HRhs)BRhs)as[BRight BEqual].
 destruct(sf_relation_total M SFEqual(code_numeral M 1)(succM M(succM M a)))as(va&HVA).
 destruct(sf_relation_total M SFEqual(zeroM M)(succM M(succM M a)))as(wa&HWA).
 destruct(sf_relation_total M SFImpl wa equal)as(forkTail&HForkTail).
 destruct(sf_relation_total M SFImpl va forkTail)as(fork&HFork).
 pose proof(source_zfr_equal_common_right M(code_numeral M 1)(zeroM M)(succM M(succM M a))va wa equal forkTail fork(succM M(succM M k))
  (proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))(coding_zero_lt_succ M k))(coding_zero_lt_succ M(succM M k))
  (proj2(coding_lt_succ_cancel M(succM M a)(succM M k))(proj2(coding_lt_succ_cancel M a k)BA))
  HVA HWA HEqual HForkTail HFork)as PFork.
 destruct PFork as(cb&cc&cn&HClosed&PFork).
 pose proof(source_zfr_context_closed M cb cc cn HClosed)as CClosed.
 pose proof(context_bounded_monotone M cb cc cn(zeroM M)k CClosed(coding_zero_lt_succ M k))as C0.
 destruct(environment_cons_total M cb cc cn af)as(b1&c1&n1&H1).
 pose proof(proj2(context_bounded_cons M cb cc cn af b1 c1 n1 k H1)(conj BAF C0))as C1.
 destruct(environment_cons_total M b1 c1 n1 ag)as(b2&c2&n2&H2).
 pose proof(proj2(context_bounded_cons M b1 c1 n1 ag b2 c2 n2 k H2)(conj BAG C1))as C2.
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M f))as(af1&HAF1).
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M g))as(ag1&HAG1).
 destruct(source_rec_attempt_total M phi(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))(succM M(succM M f)))as(af2&HAF2).
 destruct(source_rec_attempt_total M phi(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))(succM M(succM M g)))as(ag2&HAG2).
 pose proof(source_rec_attempt_shift M phi o a N f af af1 BP HAF HAF1)as SAF1.
 pose proof(source_rec_attempt_shift M phi o a N g ag ag1 BP HAG HAG1)as SAG1.
 pose proof(source_rec_attempt_shift M phi(succM M o)(succM M a)(succM M N)(succM M f)af1 af2 BP HAF1 HAF2)as SAF2.
 pose proof(source_rec_attempt_shift M phi(succM M o)(succM M a)(succM M N)(succM M g)ag1 ag2 BP HAG1 HAG2)as SAG2.
 destruct(environment_cons_total M cb cc cn af1)as(s1&t1&l1&HS1).
 assert(EL1:l1=n1)by(rewrite(proj1 HS1),(proj1 H1);reflexivity). subst l1.
 destruct(environment_cons_total M s1 t1 n1 ag1)as(s2&t2&l2&HS2).
 assert(EL2:l2=n2)by(rewrite(proj1 HS2),(proj1 H2);reflexivity). subst l2.
 pose proof(context_renaming_cons M cb cc cn(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)cb cc af af1 b1 c1 n1 s1 t1
  (source_closed_context_shift_self M cb cc cn CClosed)SAF1 H1 HS1)as Shift1a.
 pose proof(context_renaming_cons M b1 c1 n1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)s1 t1 ag ag1 b2 c2 n2 s2 t2 Shift1a SAG1 H2 HS2)as Shift1.
 pose proof(context_shift_preserves_bound M b2 c2 n2 s2 t2 k Shift1 C2)as CS.
 destruct(environment_cons_total M cb cc cn af2)as(u1&v1&m1&HU1).
 assert(EM1:m1=n1)by(rewrite(proj1 HU1),(proj1 H1);reflexivity). subst m1.
 destruct(environment_cons_total M u1 v1 n1 ag2)as(u2&v2&m2&HU2).
 assert(EM2:m2=n2)by(rewrite(proj1 HU2),(proj1 H2);reflexivity). subst m2.
 pose proof(context_renaming_cons M cb cc cn(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)cb cc af1 af2 s1 t1 n1 u1 v1
  (source_closed_context_shift_self M cb cc cn CClosed)SAF2 HS1 HU1)as Shift2a.
 pose proof(context_renaming_cons M s1 t1 n1(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)u1 v1 ag1 ag2 s2 t2 n2 u2 v2 Shift2a SAG2 HS2 HU2)as Shift2.
 pose proof(context_shift_preserves_bound M s2 t2 n2 u2 v2(succM M k)Shift2 CS)as CU.
 destruct(environment_cons_total M u2 v2 n2 left)as(b3&c3&n3&H3).
 pose proof(proj2(context_bounded_cons M u2 v2 n2 left b3 c3 n3(succM M(succM M k))H3)(conj BLeft CU))as C3.
 destruct(environment_cons_total M b3 c3 n3 right)as(b4&c4&n4&H4).
 pose proof(proj2(context_bounded_cons M b3 c3 n3 right b4 c4 n4(succM M(succM M k))H4)(conj BRight C3))as C4.
 assert(InBackground:context_included M cb cc cn b4 c4 n4).
 { intros ax HAx. apply(source_cons_tail_inclusion M b3 c3 n3 right b4 c4 n4 H4).
   apply(source_cons_tail_inclusion M u2 v2 n2 left b3 c3 n3 H3).
   apply(source_cons_tail_inclusion M u1 v1 n1 ag2 u2 v2 n2 HU2).
   exact(source_cons_tail_inclusion M cb cc cn af2 u1 v1 n1 HU1 ax HAx). }
 pose proof(source_full_prv_weaken_bounded M cb cc cn b4 c4 n4 fork(succM M(succM M k))PFork InBackground C4)as PFork4.
 assert(PAF2:source_full_prv M b4 c4 n4 af2).
 { apply full_source_Ctx.
   - exists(succM M(succM M k)). split;[exact(source_shift_bound M af1 af2(succM M k)(source_shift_bound M af af1 k BAF SAF1)SAF2)|exact C4].
   - apply(source_cons_tail_inclusion M b3 c3 n3 right b4 c4 n4 H4).
     apply(source_cons_tail_inclusion M u2 v2 n2 left b3 c3 n3 H3).
     apply(source_cons_tail_inclusion M u1 v1 n1 ag2 u2 v2 n2 HU2).
     apply(proj2(context_member_cons M cb cc cn af2 u1 v1 n1 af2 HU1)). now left. }
 assert(PAG2:source_full_prv M b4 c4 n4 ag2).
 { apply full_source_Ctx.
   - exists(succM M(succM M k)). split;[exact(source_shift_bound M ag1 ag2(succM M k)(source_shift_bound M ag ag1 k BAG SAG1)SAG2)|exact C4].
   - apply(source_cons_tail_inclusion M b3 c3 n3 right b4 c4 n4 H4).
     apply(source_cons_tail_inclusion M u2 v2 n2 left b3 c3 n3 H3).
     apply(proj2(context_member_cons M u1 v1 n1 ag2 u2 v2 n2 ag2 HU2)). now left. }
 pose proof(source_full_cons_head M u2 v2 n2 left b3 c3 n3(succM M(succM M k))H3 BLeft C3)as PLeft3.
 pose proof(source_full_cons_weaken M b3 c3 n3 right b4 c4 n4(succM M(succM M k))left H4 C4 PLeft3)as PLeft4.
 pose proof(source_full_cons_head M b3 c3 n3 right b4 c4 n4(succM M(succM M k))H4 BRight C4)as PRight4.
 pose proof(source_full_rec_agreement_zero_values M b4 c4 n4 phi(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))
  (succM M(succM M f))(succM M(succM M g))af2 ag2(code_numeral M 1)(zeroM M)left right va wa equal forkTail fork
  HAF2 HAG2 HLeft HRight HVA HWA HEqual HForkTail HFork PAF2 PAG2 PLeft4 PRight4 PFork4)as PEqual.
 pose proof(full_source_II M b3 c3 n3 right equal rhs b4 c4 n4(ex_intro _ (succM M(succM M k))(conj BRhs C3))PEqual H4 HRhs)as PRhs.
 pose proof(full_source_II M u2 v2 n2 left rhs point b3 c3 n3(ex_intro _ (succM M(succM M k))(conj BPoint CU))PRhs H3 HPoint)as PPoint.
 pose proof(full_source_AllI M s2 t2 n2 point inner u2 v2(ex_intro _ (succM M k)(conj BInner CS))PPoint Shift2 HInner)as PInner.
 pose proof(full_source_AllI M b2 c2 n2 inner agr s2 t2(ex_intro _ k(conj BAgr C2))PInner Shift1 HOuter)as PAgr.
 pose proof(full_source_II M b1 c1 n1 ag agr tail b2 c2 n2(ex_intro _ k(conj BTail C1))PAgr H2 HT)as PTail.
 exists cb,cc,cn. split;[exact HClosed|].
 exact(full_source_II M cb cc cn af tail result b1 c1 n1(ex_intro _ k(conj BResult C0))PTail H1 HR).
Qed.
Print Assumptions source_zfr_rec_agreement_zero.
