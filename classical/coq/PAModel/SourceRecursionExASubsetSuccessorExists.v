(** Eliminate the actual successor-in-N witness, then obtain it from STot. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceClosedShift
 NumericalContexts NumericalSourceFull SourceTraceBounds SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport SourceRecursionAtomicShift
 SourceRecursionTotalRelation SourceRecursionExistsAttempt SourceRecursionExASubset SourceRecursionExASubsetTransport
 SourceRecursionExASubsetRules SourceRecursionSuccessorIn SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceRecursionInductionShells
 SourceRecursionInductionTransport SourceRecursionExASubsetSuccessorBranch SourceDerivedRules SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_succ_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_succ_bound].
Theorem source_zfr_rec_exa_subset_successor_exists M phi o a N X z totalG nonzero inj chart mx exN target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M X k ->coding_lt M z k ->source_rec_total_relation M phi totalG ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->
 source_rec_exa_subset_chart M phi o a N X chart ->sf_relation M SFMember z X mx ->source_rec_successor_in M z N exN ->source_rec_successor_in M z X target ->
 source_finite_telescope M[totalG;nonzero;inj;chart;mx;exN]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BX BZ HFun HAF HAG HChart HMX HExN HTarget HLaw.
 destruct(source_rec_nonzero_total M(succM M o)(succM M N))as(nonzero1&HAF1).
 destruct(source_rec_injectivity_total M(succM M N))as(inj1&HAG1).
 destruct(source_rec_exa_subset_chart_total M phi(succM M o)(succM M a)(succM M N)(succM M X))as(chart1&HChart1).
 destruct(sf_relation_total M SFMember(succM M z)(succM M X))as(mx1&HMX1).
 destruct(source_rec_successor_in_total M(succM M z)(succM M X))as(target1&HTarget1).
 pose proof(source_closed_shift_self M totalG(source_rec_total_relation_closed M phi totalG BP HFun))as SFun.
 pose proof(source_rec_nonzero_shift M o N nonzero nonzero1 HAF HAF1)as SAF.
 pose proof(source_rec_injectivity_shift M N inj inj1 HAG HAG1)as SAG.
 pose proof(source_rec_exa_subset_chart_shift M phi o a N X chart chart1 BP HChart HChart1)as SChart.
 pose proof(source_rec_member_shift M z X mx mx1 HMX HMX1)as SMX.
 pose proof(source_rec_successor_in_shift M z X target target1 HTarget HTarget1)as STarget.
 destruct HExN as(successor&mn&body&HS&HMN&HBody&HEx).
 destruct(source_finite_telescope_total M[totalG;nonzero1;inj1;chart1;mx1;body]target1)as(branchLaw&HBranchLaw).
 assert(PBranch:source_zfr_provable M branchLaw).
 { apply(source_zfr_rec_exa_subset_successor_branch M phi(succM M o)(succM M a)(succM M N)(succM M X)(succM M z)(zeroM M)
   totalG nonzero1 inj1 chart1 mx1 successor mn body target1 branchLaw(succM M k));try rec_succ_bound;assumption. }
 assert(BFun:source_bounded M totalG k)by exact(source_bounded_monotone M totalG(zeroM M)k(source_rec_total_relation_closed M phi totalG BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M nonzero k)by exact(source_rec_nonzero_bounded M o N nonzero k BO BN HAF).
 assert(BAG:source_bounded M inj k)by exact(source_rec_injectivity_bounded M N inj k BN HAG).
 pose proof(source_rec_exa_subset_chart_bounded M phi o a N X chart k BP BO BA BN BX HChart)as BChart.
 assert(BMX:source_bounded M mx k)by exact(proj2(source_bounded_accept_atom M SFMember z X mx k(or_introl eq_refl)HMX)(conj BZ BX)).
 assert(BEx:source_bounded M exN k).
 { exact(source_rec_successor_in_bounded M z N exN k BZ BN(ex_intro _ successor(ex_intro _ mn(ex_intro _ body(conj HS(conj HMN(conj HBody HEx))))))). }
 pose proof(source_rec_successor_in_bounded M z X target k BZ BX HTarget)as BTarget.
 apply(source_zfr_finite_telescope_exists M[totalG;nonzero;inj;chart;mx][totalG;nonzero1;inj1;chart1;mx1]body exN target target1 branchLaw law k).
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

Theorem source_zfr_rec_exa_subset_successor M phi o a N X z totalG nonzero inj totality chart mx target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M X k ->coding_lt M z k ->source_rec_total_relation M phi totalG ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->
 source_rec_totality M N totality ->source_rec_exa_subset_chart M phi o a N X chart ->sf_relation M SFMember z X mx ->source_rec_successor_in M z X target ->
 source_finite_telescope M[totalG;nonzero;inj;totality;chart;mx]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BX BZ HFun HAF HAG HTotality HChart HMX HTarget HLaw.
 destruct(source_zfr_rec_totality_use_total M N z)as(totality'&mn&exN&tail&totalLaw&HT'&HMN&HExN&HTail&HTotalLaw&PTotalLaw).
 pose proof(code_relation_functional M _ _ totality' totality HT' HTotality)as E. subst totality'.
 destruct(source_finite_telescope_total M[totalG;nonzero;inj;chart;mx;exN]target)as(exLaw&HExLaw).
 pose proof(source_zfr_rec_exa_subset_successor_exists M phi o a N X z totalG nonzero inj chart mx exN target exLaw k
  BP BO BA BN BX BZ HFun HAF HAG HChart HMX HExN HTarget HExLaw)as PExLaw.
 assert(BFun:source_bounded M totalG k)by exact(source_bounded_monotone M totalG(zeroM M)k(source_rec_total_relation_closed M phi totalG BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M nonzero k)by exact(source_rec_nonzero_bounded M o N nonzero k BO BN HAF).
 assert(BAG:source_bounded M inj k)by exact(source_rec_injectivity_bounded M N inj k BN HAG).
 pose proof(source_rec_totality_bounded M N totality k BN HTotality)as BTotality.
 pose proof(source_rec_exa_subset_chart_bounded M phi o a N X chart k BP BO BA BN BX HChart)as BChart.
 assert(BMX:source_bounded M mx k)by exact(proj2(source_bounded_accept_atom M SFMember z X mx k(or_introl eq_refl)HMX)(conj BZ BX)).
 pose proof(source_rec_successor_in_bounded M z X target k BZ BX HTarget)as BTarget.
 apply(source_zfr_finite_rule M[totalLaw;exLaw][totalG;nonzero;inj;totality;chart;mx]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PFun:source_full_prv M cb cc cn totalG)by(apply Premises;cbn;tauto).
   assert(PAF:source_full_prv M cb cc cn nonzero)by(apply Premises;cbn;tauto).
   assert(PAG:source_full_prv M cb cc cn inj)by(apply Premises;cbn;tauto).
   assert(PTotality:source_full_prv M cb cc cn totality)by(apply Premises;cbn;tauto).
   assert(PChart:source_full_prv M cb cc cn chart)by(apply Premises;cbn;tauto).
   assert(PMX:source_full_prv M cb cc cn mx)by(apply Premises;cbn;tauto).
   destruct(source_rec_exa_total M phi z o a N)as(agr&HA).
   destruct(source_full_rec_exa_subset_chart_out M cb cc cn phi o a N X z chart mx mn agr BP HChart HMX HMN HA PChart PMX)as[PMN PA].
   pose proof(source_full_modus_ponens M cb cc cn totality tail totalLaw HTotalLaw(Laws totalLaw(or_introl eq_refl))PTotality)as PTail.
   pose proof(source_full_modus_ponens M cb cc cn mn exN tail HTail PTail PMN)as PExN.
   apply(source_full_finite_telescope_apply M[totalG;nonzero;inj;chart;mx;exN]target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
Qed.
Print Assumptions source_zfr_rec_exa_subset_successor_exists.
Print Assumptions source_zfr_rec_exa_subset_successor.
