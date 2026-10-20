(** The agreement subset is successor closed, with the fresh variable discharged. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceRecursionPrimitiveRelations
 SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs SourceRecursionFunctionality SourceRecursionFunctionalityClosed
 SourceRecursionAgreementSubset SourceRecursionSubsetBounds SourceRecursionInductionGraphs SourceRecursionInductionBounds
 SourceRecursionInductionTransport SourceRecursionSuccessorIn SourceRecursionSubsetSuccessorExists SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_closed_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_closed_bound].
Theorem source_zfr_rec_subset_closed M phi o a N f g X funlaw af ag totality chart closed law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->coding_lt M X k ->
 source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_totality M N totality ->source_rec_subset_chart M f g N X chart ->source_rec_successor_closed M X closed ->
 source_finite_telescope M[funlaw;af;ag;totality;chart]closed law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BX HFun HAF HAG HTotality HChart HClosed HLaw.
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M f))as(af1&HAF1).
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M g))as(ag1&HAG1).
 destruct(source_rec_totality_total M(succM M N))as(totality1&HTotality1).
 destruct(source_rec_subset_chart_total M(succM M f)(succM M g)(succM M N)(succM M X))as(chart1&HChart1).
 pose proof(source_rec_functionality_shift M phi funlaw BP HFun)as SFun.
 pose proof(source_rec_attempt_shift M phi o a N f af af1 BP HAF HAF1)as SAF.
 pose proof(source_rec_attempt_shift M phi o a N g ag ag1 BP HAG HAG1)as SAG.
 pose proof(source_rec_totality_shift M N totality totality1 HTotality HTotality1)as STotality.
 pose proof(source_rec_subset_chart_shift M f g N X chart chart1 HChart HChart1)as SChart.
 pose proof(source_rec_successor_closed_bounded M X closed k BX HClosed)as BClosed.
 destruct HClosed as(member&ex&point&HM&HE&HP&HA).
 pose proof(proj1(source_bounded_accept_unary M SFAll point closed k(or_introl eq_refl)HA)BClosed)as BPoint.
 destruct(source_finite_telescope_total M[funlaw;af1;ag1;totality1;chart1]point)as(pointLaw&HPointLaw).
 assert(HSuccessorLaw:source_finite_telescope M[funlaw;af1;ag1;totality1;chart1;member]ex pointLaw).
 { apply(source_finite_telescope_prefix M[funlaw;af1;ag1;totality1;chart1][member]point ex pointLaw HPointLaw).
   exists ex. split;[reflexivity|exact HP]. }
 assert(PPoint:source_zfr_provable M pointLaw).
 { apply(source_zfr_rec_subset_successor M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M g)(succM M X)(zeroM M)
    funlaw af1 ag1 totality1 chart1 member ex pointLaw(succM M k));try rec_closed_bound;assumption. }
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M af k)by exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 assert(BAG:source_bounded M ag k)by exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
 pose proof(source_rec_totality_bounded M N totality k BN HTotality)as BTotality.
 pose proof(source_rec_subset_chart_bounded M f g N X chart k BF BG BN BX HChart)as BChart.
 apply(source_zfr_finite_telescope_all M[funlaw;af;ag;totality;chart][funlaw;af1;ag1;totality1;chart1]point closed pointLaw law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption.
 - exact BPoint.
 - repeat(constructor;[assumption|]). constructor.
 - exact HA.
 - exact HPointLaw.
 - exact HLaw.
 - exact PPoint.
Qed.
Print Assumptions source_zfr_rec_subset_closed.
