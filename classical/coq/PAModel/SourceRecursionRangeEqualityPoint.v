(** Actual equality of two values of two chosen attempts at one domain index. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionInductionGraphs SourceRecursionInductionBounds
 SourceRecursionAgreement SourceRecursionAgreementOn SourceRecursionAgreementOnUse SourceRecursionAttemptsAgree SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_range_equality_point M phi o a N f g z v w funlaw af ag totality induction member mz appf appg equal law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->
 source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_totality M N totality ->source_rec_induction M o N induction ->sf_relation M SFMember o N member ->sf_relation M SFMember z N mz ->
 source_rec_app M f z v appf ->source_rec_app M g z w appg ->sf_relation M SFEqual v w equal ->
 source_finite_telescope M[funlaw;af;ag;totality;induction;member;mz;appf;appg]equal law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BZ BV BW HFun HAF HAG HT HI HM HMZ HAppF HAppG HE HLaw.
 destruct(source_rec_agrees_on_total M f g N)as(agree&HAgree).
 destruct(source_finite_telescope_total M[funlaw;af;ag;totality;induction;member]agree)as(agreeLaw&HAgreeLaw).
 pose proof(source_zfr_rec_attempts_agree M phi o a N f g funlaw af ag totality induction member agree agreeLaw k BP BO BA BN BF BG HFun HAF HAG HT HI HM HAgree HAgreeLaw)as PAgreeLaw.
 pose proof(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF)as BAF.
 pose proof(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG)as BAG.
 pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
 pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
 pose proof(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k))as BFun.
 pose proof(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN))as BM.
 pose proof(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN))as BMZ.
 pose proof(source_rec_app_bounded M f z v appf k BF BZ BV HAppF)as BAppF.
 pose proof(source_rec_app_bounded M g z w appg k BG BZ BW HAppG)as BAppG.
 pose proof(proj2(source_bounded_accept_atom M SFEqual v w equal k(or_intror eq_refl)HE)(conj BV BW))as BE.
 apply(source_zfr_finite_rule M[agreeLaw][funlaw;af;ag;totality;induction;member;mz;appf;appg]equal law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];assumption.
 - exact BE.
 - exact HLaw.
 - intros x[<-|[]]. exact PAgreeLaw.
 - intros cb cc cn BC Laws Premises.
   assert(PAgree:source_full_prv M cb cc cn agree).
   { apply(source_full_finite_telescope_apply M[funlaw;af;ag;totality;induction;member]agree agreeLaw HAgreeLaw cb cc cn).
     - apply Laws. now left.
     - intros x HX. apply Premises. cbn in HX|-*. tauto. }
   destruct(source_rec_agreement_total M f g z)as(agr&HAgr).
   pose proof(source_full_rec_agrees_on_use M cb cc cn f g N agree z mz agr HAgree HMZ HAgr PAgree(Premises mz ltac:(cbn;tauto)))as PAgr.
   exact(source_full_rec_agreement_use M cb cc cn f g z agr v w appf appg equal HAgr HAppF HAppG HE PAgr
    (Premises appf ltac:(cbn;tauto))(Premises appg ltac:(cbn;tauto))).
Qed.
Print Assumptions source_zfr_rec_range_equality_point.
