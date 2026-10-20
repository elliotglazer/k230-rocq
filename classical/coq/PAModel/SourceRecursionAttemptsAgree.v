(** Uniform agreement of arbitrary internally coded recursion attempts.
    The Agr Separation witness, its SInd induction and every quantifier
    are discharged in the numerical source proof calculus. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs SourceRecursionAtomicShift
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceRecursionInductionShift
 SourceRecursionInductionTransport SourceRecursionAgreementSubset SourceRecursionAgreementSeparation SourceRecursionSubsetBounds
 SourceRecursionAgreementOn SourceRecursionAgreementInduction SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_agree_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_agree_bound].
Theorem source_zfr_rec_attempts_agree M phi o a N f g funlaw af ag totality induction member target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_totality M N totality ->source_rec_induction M o N induction ->sf_relation M SFMember o N member ->
 source_rec_agrees_on M f g N target ->source_finite_telescope M[funlaw;af;ag;totality;induction;member]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG HFun HAF HAG HT HI HM HTarget HLaw.
 destruct(source_zfr_rec_agreement_subset_exists M f g N)as(ex&body&HChart&HEx&PEx).
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M f))as(af1&HAF1).
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M g))as(ag1&HAG1).
 destruct(source_rec_totality_total M(succM M N))as(totality1&HT1).
 destruct(source_rec_induction_total M(succM M o)(succM M N))as(induction1&HI1).
 destruct(sf_relation_total M SFMember(succM M o)(succM M N))as(member1&HM1).
 destruct(source_rec_agrees_on_total M(succM M f)(succM M g)(succM M N))as(target1&HTarget1).
 pose proof(source_rec_functionality_shift M phi funlaw BP HFun)as SFun.
 pose proof(source_rec_attempt_shift M phi o a N f af af1 BP HAF HAF1)as SAF.
 pose proof(source_rec_attempt_shift M phi o a N g ag ag1 BP HAG HAG1)as SAG.
 pose proof(source_rec_totality_shift M N totality totality1 HT HT1)as ST.
 pose proof(source_rec_induction_shift M o N induction induction1 HI HI1)as SI.
 pose proof(source_rec_member_shift M o N member member1 HM HM1)as SM.
 pose proof(source_rec_agrees_on_shift M f g N target target1 HTarget HTarget1)as STarget.
 destruct(source_finite_telescope_total M[funlaw;af1;ag1;totality1;induction1;member1;body]target1)as(branchLaw&HBranchLaw).
 assert(PBranch:source_zfr_provable M branchLaw).
 { apply(source_zfr_rec_agreement_induction M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M g)(zeroM M)
   funlaw af1 ag1 totality1 induction1 member1 body target1 branchLaw(succM M k));try rec_agree_bound;assumption. }
 pose proof(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF)as BAF.
 pose proof(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG)as BAG.
 pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
 pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BM:source_bounded M member k)by exact(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN)).
 pose proof(source_rec_agrees_on_bounded M f g N target k BF BG BN HTarget)as BTarget.
 assert(BEx:source_bounded M ex k).
 { apply(proj2(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)).
   exact(source_rec_subset_chart_bounded M(succM M f)(succM M g)(succM M N)(zeroM M)body(succM M k)
    (proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M g k)BG)(proj2(coding_lt_succ_cancel M N k)BN)(coding_zero_lt_succ M k)HChart). }
 destruct(source_finite_telescope_total M[funlaw;af;ag;totality;induction;member;ex]target)as(exLaw&HExLaw).
 assert(PExLaw:source_zfr_provable M exLaw).
 { apply(source_zfr_finite_telescope_exists M[funlaw;af;ag;totality;induction;member][funlaw;af1;ag1;totality1;induction1;member1]
   body ex target target1 branchLaw exLaw k).
   - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
   - exact BEx.
   - exact BTarget.
   - repeat(constructor;[assumption|]). constructor.
   - exact HEx.
   - exact STarget.
   - exact HBranchLaw.
   - exact HExLaw.
   - exact PBranch. }
 apply(source_zfr_finite_rule M[ex;exLaw][funlaw;af;ag;totality;induction;member]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   apply(source_full_finite_telescope_apply M[funlaw;af;ag;totality;induction;member;ex]target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
     all:first[apply Premises;cbn;tauto|apply Laws;now left].
Qed.
Print Assumptions source_zfr_rec_attempts_agree.
