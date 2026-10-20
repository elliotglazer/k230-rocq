(** Actual SInd applied to the agreement subset. All finite laws are proved ZFR laws. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceDerivedRules SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceRecursionInductionShells
 SourceRecursionAgreementSubset SourceRecursionSubsetBounds SourceRecursionSubsetClosed SourceRecursionSubsetZero SourceRecursionAgreementOn SourceRecursionAgreementOnSubset
 SourceRecursionSuccessorIn SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_agreement_induction M phi o a N f g X funlaw af ag totality induction member chart target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->coding_lt M X k ->
 source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_totality M N totality ->source_rec_induction M o N induction ->sf_relation M SFMember o N member ->
 source_rec_subset_chart M f g N X chart ->source_rec_agrees_on M f g N target ->
 source_finite_telescope M[funlaw;af;ag;totality;induction;member;chart]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BX HFun HAF HAG HT HI HM HC HTarget HLaw.
 destruct(source_zfr_rec_induction_use_total M o N X)as(induction'&mx&closed&subset&t1&t2&inductionLaw&HI'&HMX&HClosed&HSubset&H2&H1&HL&PInductionLaw).
 pose proof(code_relation_functional M _ _ induction' induction HI' HI)as E. subst induction'.
 destruct(source_finite_telescope_total M[af;ag;chart;member]mx)as(baseLaw&HBaseLaw).
 pose proof(source_zfr_rec_subset_zero M phi o a N f g X af ag chart member mx baseLaw k BP BO BA BN BF BG BX HAF HAG HC HM HMX HBaseLaw)as PBaseLaw.
 destruct(source_finite_telescope_total M[funlaw;af;ag;totality;chart]closed)as(closedLaw&HClosedLaw).
 pose proof(source_zfr_rec_subset_closed M phi o a N f g X funlaw af ag totality chart closed closedLaw k BP BO BA BN BF BG BX HFun HAF HAG HT HC HClosed HClosedLaw)as PClosedLaw.
 destruct(source_finite_telescope_total M[chart;subset]target)as(chartLaw&HChartLaw).
 pose proof(source_zfr_rec_agreement_on_subset M f g N X chart subset target chartLaw k BF BG BN BX HC HSubset HTarget HChartLaw)as PChartLaw.
 pose proof(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF)as BAF.
 pose proof(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG)as BAG.
 pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
 pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
 pose proof(source_rec_subset_chart_bounded M f g N X chart k BF BG BN BX HC)as BC.
 assert(BF':source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BM:source_bounded M member k)by exact(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN)).
 pose proof(source_rec_agrees_on_bounded M f g N target k BF BG BN HTarget)as BTarget.
 apply(source_zfr_finite_rule M[baseLaw;closedLaw;inductionLaw;chartLaw][funlaw;af;ag;totality;induction;member;chart]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[<-|[<-|[]]]]];assumption.
 - intros cb cc cn BContext Laws Premises.
   assert(PFun:source_full_prv M cb cc cn funlaw)by(apply Premises;cbn;tauto).
   assert(PAF:source_full_prv M cb cc cn af)by(apply Premises;cbn;tauto).
   assert(PAG:source_full_prv M cb cc cn ag)by(apply Premises;cbn;tauto).
   assert(PT:source_full_prv M cb cc cn totality)by(apply Premises;cbn;tauto).
   assert(PI:source_full_prv M cb cc cn induction)by(apply Premises;cbn;tauto).
   assert(PMember:source_full_prv M cb cc cn member)by(apply Premises;cbn;tauto).
   assert(PChart:source_full_prv M cb cc cn chart)by(apply Premises;cbn;tauto).
   assert(PMX:source_full_prv M cb cc cn mx).
   { apply(source_full_finite_telescope_apply M[af;ag;chart;member]mx baseLaw HBaseLaw cb cc cn).
     - apply Laws. now left.
     - intros x[<-|[<-|[<-|[<-|[]]]]];assumption. }
   assert(PClosed:source_full_prv M cb cc cn closed).
   { apply(source_full_finite_telescope_apply M[funlaw;af;ag;totality;chart]closed closedLaw HClosedLaw cb cc cn).
     - apply Laws. right. now left.
     - intros x[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption. }
   pose proof(source_full_modus_ponens M cb cc cn induction t1 inductionLaw HL(Laws inductionLaw(or_intror(or_intror(or_introl eq_refl))))PI)as P1.
   pose proof(source_full_modus_ponens M cb cc cn mx t2 t1 H1 P1 PMX)as P2.
   pose proof(source_full_modus_ponens M cb cc cn closed subset t2 H2 P2 PClosed)as PSubset.
   apply(source_full_finite_telescope_apply M[chart;subset]target chartLaw HChartLaw cb cc cn).
   + apply Laws. right. right. right. now left.
   + intros x[<-|[<-|[]]];assumption.
Qed.
Print Assumptions source_zfr_rec_agreement_induction.
