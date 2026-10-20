(** Eliminate the actual successor-in-N witness, then obtain it from STot. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalSourceFull SourceTraceBounds SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs SourceRecursionAtomicShift
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionAgreement SourceRecursionAgreementSubset SourceRecursionSubsetBounds
 SourceRecursionSubsetRules SourceRecursionSuccessorIn SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceRecursionInductionShells
 SourceRecursionInductionTransport SourceRecursionSubsetSuccessorBranch SourceDerivedRules SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_succ_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_succ_bound].
Theorem source_zfr_rec_subset_successor_exists M phi o a N f g X z funlaw af ag chart mx exN target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M X k ->coding_lt M z k ->source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_subset_chart M f g N X chart ->sf_relation M SFMember z X mx ->source_rec_successor_in M z N exN ->source_rec_successor_in M z X target ->
 source_finite_telescope M[funlaw;af;ag;chart;mx;exN]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BX BZ HFun HAF HAG HChart HMX HExN HTarget HLaw.
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M f))as(af1&HAF1).
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M g))as(ag1&HAG1).
 destruct(source_rec_subset_chart_total M(succM M f)(succM M g)(succM M N)(succM M X))as(chart1&HChart1).
 destruct(sf_relation_total M SFMember(succM M z)(succM M X))as(mx1&HMX1).
 destruct(source_rec_successor_in_total M(succM M z)(succM M X))as(target1&HTarget1).
 pose proof(source_rec_functionality_shift M phi funlaw BP HFun)as SFun.
 pose proof(source_rec_attempt_shift M phi o a N f af af1 BP HAF HAF1)as SAF.
 pose proof(source_rec_attempt_shift M phi o a N g ag ag1 BP HAG HAG1)as SAG.
 pose proof(source_rec_subset_chart_shift M f g N X chart chart1 HChart HChart1)as SChart.
 pose proof(source_rec_member_shift M z X mx mx1 HMX HMX1)as SMX.
 pose proof(source_rec_successor_in_shift M z X target target1 HTarget HTarget1)as STarget.
 destruct HExN as(successor&mn&body&HS&HMN&HBody&HEx).
 destruct(source_finite_telescope_total M[funlaw;af1;ag1;chart1;mx1;body]target1)as(branchLaw&HBranchLaw).
 assert(PBranch:source_zfr_provable M branchLaw).
 { apply(source_zfr_rec_subset_successor_branch M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M g)(succM M X)(succM M z)(zeroM M)
   funlaw af1 ag1 chart1 mx1 successor mn body target1 branchLaw(succM M k));try rec_succ_bound;assumption. }
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M af k)by exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 assert(BAG:source_bounded M ag k)by exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
 pose proof(source_rec_subset_chart_bounded M f g N X chart k BF BG BN BX HChart)as BChart.
 assert(BMX:source_bounded M mx k)by exact(proj2(source_bounded_accept_atom M SFMember z X mx k(or_introl eq_refl)HMX)(conj BZ BX)).
 assert(BEx:source_bounded M exN k).
 { exact(source_rec_successor_in_bounded M z N exN k BZ BN(ex_intro _ successor(ex_intro _ mn(ex_intro _ body(conj HS(conj HMN(conj HBody HEx))))))). }
 pose proof(source_rec_successor_in_bounded M z X target k BZ BX HTarget)as BTarget.
 apply(source_zfr_finite_telescope_exists M[funlaw;af;ag;chart;mx][funlaw;af1;ag1;chart1;mx1]body exN target target1 branchLaw law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption.
 - exact BEx.
 - exact BTarget.
 - repeat(constructor;[assumption|]). constructor.
 - exact HEx.
 - exact STarget.
 - exact HBranchLaw.
 - exact HLaw.
 - exact PBranch.
Qed.

Theorem source_zfr_rec_subset_successor M phi o a N f g X z funlaw af ag totality chart mx target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M X k ->coding_lt M z k ->source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_totality M N totality ->source_rec_subset_chart M f g N X chart ->sf_relation M SFMember z X mx ->source_rec_successor_in M z X target ->
 source_finite_telescope M[funlaw;af;ag;totality;chart;mx]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BX BZ HFun HAF HAG HTotality HChart HMX HTarget HLaw.
 destruct(source_zfr_rec_totality_use_total M N z)as(totality'&mn&exN&tail&totalLaw&HT'&HMN&HExN&HTail&HTotalLaw&PTotalLaw).
 pose proof(code_relation_functional M _ _ totality' totality HT' HTotality)as E. subst totality'.
 destruct(source_finite_telescope_total M[funlaw;af;ag;chart;mx;exN]target)as(exLaw&HExLaw).
 pose proof(source_zfr_rec_subset_successor_exists M phi o a N f g X z funlaw af ag chart mx exN target exLaw k
  BP BO BA BN BF BG BX BZ HFun HAF HAG HChart HMX HExN HTarget HExLaw)as PExLaw.
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M af k)by exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 assert(BAG:source_bounded M ag k)by exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
 pose proof(source_rec_totality_bounded M N totality k BN HTotality)as BTotality.
 pose proof(source_rec_subset_chart_bounded M f g N X chart k BF BG BN BX HChart)as BChart.
 assert(BMX:source_bounded M mx k)by exact(proj2(source_bounded_accept_atom M SFMember z X mx k(or_introl eq_refl)HMX)(conj BZ BX)).
 pose proof(source_rec_successor_in_bounded M z X target k BZ BX HTarget)as BTarget.
 apply(source_zfr_finite_rule M[totalLaw;exLaw][funlaw;af;ag;totality;chart;mx]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PFun:source_full_prv M cb cc cn funlaw)by(apply Premises;cbn;tauto).
   assert(PAF:source_full_prv M cb cc cn af)by(apply Premises;cbn;tauto).
   assert(PAG:source_full_prv M cb cc cn ag)by(apply Premises;cbn;tauto).
   assert(PTotality:source_full_prv M cb cc cn totality)by(apply Premises;cbn;tauto).
   assert(PChart:source_full_prv M cb cc cn chart)by(apply Premises;cbn;tauto).
   assert(PMX:source_full_prv M cb cc cn mx)by(apply Premises;cbn;tauto).
   destruct(source_rec_agreement_total M f g z)as(agr&HA).
   destruct(source_full_rec_subset_chart_out M cb cc cn f g N X z chart mx mn agr HChart HMX HMN HA PChart PMX)as[PMN PA].
   pose proof(source_full_modus_ponens M cb cc cn totality tail totalLaw HTotalLaw(Laws totalLaw(or_introl eq_refl))PTotality)as PTail.
   pose proof(source_full_modus_ponens M cb cc cn mn exN tail HTail PTail PMN)as PExN.
   apply(source_full_finite_telescope_apply M[funlaw;af;ag;chart;mx;exN]target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
Qed.
Print Assumptions source_zfr_rec_subset_successor_exists.
Print Assumptions source_zfr_rec_subset_successor.
