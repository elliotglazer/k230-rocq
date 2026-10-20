(** The chosen-value step of recursion closure. Actual attempt agreement
    identifies the two inputs; RR and its range chart put the next value in Y. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull SourceDerivedRules
  SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability SourceRecursionPrimitiveRelations
  SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionFunctionality
  SourceRecursionFunctionalityClosed SourceRecursionInductionGraphs SourceRecursionInductionBounds
  SourceRecursionBinaryInstance SourceRecursionAgreementPoints SourceRecursionRangeEqualityPoint
  SourceRecursionRangeRelation SourceRecursionRangeIntroduction SourceRecursionRangeFibre
  SourceRecursionRangeChart SourceRecursionRangeChartRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_rec_closure_values M phi o a N f g z v u w next Y
    funlaw totality induction member af ag mz appf appg before appnext mnext chart
    after resultMember target law k:
  source_bounded M phi(code_numeral M 2) ->
  coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
  coding_lt M z k ->coding_lt M v k ->coding_lt M u k ->coding_lt M w k ->coding_lt M next k ->coding_lt M Y k ->
  source_rec_functionality M phi funlaw ->source_rec_totality M N totality ->
  source_rec_induction M o N induction ->sf_relation M SFMember o N member ->
  source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
  sf_relation M SFMember z N mz ->source_rec_app M f z v appf ->source_rec_app M g z u appg ->
  source_rec_binary M phi u w before ->source_rec_app M g next w appnext ->
  sf_relation M SFMember next N mnext ->source_rec_range_chart M phi o a N Y chart ->
  source_rec_binary M phi v w after ->sf_relation M SFMember w Y resultMember ->
  sf_relation M SFAnd after resultMember target ->
  source_finite_telescope M[funlaw;totality;induction;member;af;ag;mz;appf;appg;before;appnext;mnext;chart]target law ->
  source_zfr_provable M law.
Proof.
  intros BP BO BA BN BF BG BZ BV BU BW BNext BY HFun HT HI HM HAF HAG HMZ HAppF HAppG
    HBefore HAppNext HMNext HChart HAfter HResult HTarget HLaw.
  destruct(sf_relation_total M SFEqual v u)as(equal&HEq).
  destruct(source_finite_telescope_total M[funlaw;af;ag;totality;induction;member;mz;appf;appg]equal)as(equalityLaw&HEqualityLaw).
  pose proof(source_zfr_rec_range_equality_point M phi o a N f g z v u funlaw af ag totality induction member mz appf appg equal equalityLaw k
    BP BO BA BN BF BG BZ BV BU HFun HAF HAG HT HI HM HMZ HAppF HAppG HEq HEqualityLaw)as PEqualityLaw.
  destruct(sf_relation_total M SFImpl before after)as(movePoint&HMovePoint).
  destruct(sf_relation_total M SFImpl equal movePoint)as(moveLaw&HMoveLaw).
  pose proof(source_zfr_rec_agreement_transport M phi v u w before after equal movePoint moveLaw k
    BP BV BU BW HAfter HBefore HEq HMovePoint HMoveLaw)as PMoveLaw.
  pose proof(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)
    (coding_zero_lt_succ M k))as BFun.
  pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
  pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
  pose proof(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN))as BM.
  pose proof(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF)as BAF.
  pose proof(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG)as BAG.
  pose proof(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN))as BMZ.
  pose proof(source_rec_app_bounded M f z v appf k BF BZ BV HAppF)as BAppF.
  pose proof(source_rec_app_bounded M g z u appg k BG BZ BU HAppG)as BAppG.
  pose proof(source_rec_binary_bounded M phi u w before k BP BU BW HBefore)as BBefore.
  pose proof(source_rec_app_bounded M g next w appnext k BG BNext BW HAppNext)as BAppNext.
  pose proof(proj2(source_bounded_accept_atom M SFMember next N mnext k(or_introl eq_refl)HMNext)(conj BNext BN))as BMNext.
  pose proof(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart)as BChart.
  pose proof(source_rec_binary_bounded M phi v w after k BP BV BW HAfter)as BAfter.
  pose proof(proj2(source_bounded_accept_atom M SFMember w Y resultMember k(or_introl eq_refl)HResult)(conj BW BY))as BResult.
  pose proof(proj2(source_bounded_accept_binary M SFAnd after resultMember target k(or_introl eq_refl)HTarget)(conj BAfter BResult))as BTarget.
  apply(source_zfr_finite_rule M[equalityLaw;moveLaw]
    [funlaw;totality;induction;member;af;ag;mz;appf;appg;before;appnext;mnext;chart]target law k).
  - intros t HTmp. repeat(destruct HTmp as[HTmp|HTmp];[subst t;assumption|]). contradiction.
  - exact BTarget.
  - exact HLaw.
  - intros t[<-|[<-|[]]];assumption.
  - intros cb cc cn BC Laws Premises.
    assert(PEqual:source_full_prv M cb cc cn equal).
    { apply(source_full_finite_telescope_apply M[funlaw;af;ag;totality;induction;member;mz;appf;appg]equal equalityLaw HEqualityLaw cb cc cn).
      - apply Laws. now left.
      - intros t HTmp. apply Premises. cbn in HTmp|-*. tauto. }
    pose proof(source_full_modus_ponens M cb cc cn equal movePoint moveLaw HMoveLaw
      (Laws moveLaw(or_intror(or_introl eq_refl)))PEqual)as PMovePoint.
    pose proof(source_full_modus_ponens M cb cc cn before after movePoint HMovePoint PMovePoint
      (Premises before ltac:(cbn;tauto)))as PAfter.
    destruct(source_rec_rr_total M phi next w o a N)as(rr&HRR).
    pose proof(source_full_rec_rr_intro M cb cc cn phi next w o a N rr g mnext ag appnext k
      BP BNext BW BO BA BN BC HRR HMNext HAG HAppNext
      (Premises mnext ltac:(cbn;tauto))(Premises ag ltac:(cbn;tauto))(Premises appnext ltac:(cbn;tauto)))as PRR.
    destruct(source_rec_range_fibre_total M phi o a N w)as(fibre&HFibre).
    pose proof(source_full_rec_range_fibre_intro M cb cc cn phi o a N w next mnext rr fibre k
      BP BO BA BN BW BC HMNext HRR HFibre(Premises mnext ltac:(cbn;tauto))PRR)as PFibre.
    pose proof(source_full_rec_range_chart_in M cb cc cn phi o a N Y w chart resultMember fibre
      BP HChart HResult HFibre(Premises chart ltac:(cbn;tauto))PFibre)as PMember.
    exact(full_source_CI M cb cc cn after resultMember target(ex_intro _ k(conj BTarget BC))PAfter PMember HTarget).
Qed.
Print Assumptions source_zfr_rec_closure_values.
