(** The ExA subset is successor closed, with the fresh variable discharged. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceClosedShift
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceRecursionPrimitiveRelations
 SourceRecursionTotalRelation SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport
 SourceRecursionExistsAttempt SourceRecursionExASubset SourceRecursionExASubsetTransport SourceRecursionInductionGraphs SourceRecursionInductionBounds
 SourceRecursionInductionTransport SourceRecursionSuccessorIn SourceRecursionExASubsetSuccessorExists SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_closed_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_closed_bound].
Theorem source_zfr_rec_exa_subset_closed M phi o a N X totalG nonzero inj totality chart closed law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M X k ->
 source_rec_total_relation M phi totalG ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->
 source_rec_totality M N totality ->source_rec_exa_subset_chart M phi o a N X chart ->source_rec_successor_closed M X closed ->
 source_finite_telescope M[totalG;nonzero;inj;totality;chart]closed law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BX HFun HAF HAG HTotality HChart HClosed HLaw.
 destruct(source_rec_nonzero_total M(succM M o)(succM M N))as(nonzero1&HAF1).
 destruct(source_rec_injectivity_total M(succM M N))as(inj1&HAG1).
 destruct(source_rec_totality_total M(succM M N))as(totality1&HTotality1).
 destruct(source_rec_exa_subset_chart_total M phi(succM M o)(succM M a)(succM M N)(succM M X))as(chart1&HChart1).
 pose proof(source_closed_shift_self M totalG(source_rec_total_relation_closed M phi totalG BP HFun))as SFun.
 pose proof(source_rec_nonzero_shift M o N nonzero nonzero1 HAF HAF1)as SAF.
 pose proof(source_rec_injectivity_shift M N inj inj1 HAG HAG1)as SAG.
 pose proof(source_rec_totality_shift M N totality totality1 HTotality HTotality1)as STotality.
 pose proof(source_rec_exa_subset_chart_shift M phi o a N X chart chart1 BP HChart HChart1)as SChart.
 pose proof(source_rec_successor_closed_bounded M X closed k BX HClosed)as BClosed.
 destruct HClosed as(member&ex&point&HM&HE&HP&HA).
 pose proof(proj1(source_bounded_accept_unary M SFAll point closed k(or_introl eq_refl)HA)BClosed)as BPoint.
 destruct(source_finite_telescope_total M[totalG;nonzero1;inj1;totality1;chart1]point)as(pointLaw&HPointLaw).
 assert(HSuccessorLaw:source_finite_telescope M[totalG;nonzero1;inj1;totality1;chart1;member]ex pointLaw).
 { apply(source_finite_telescope_prefix M[totalG;nonzero1;inj1;totality1;chart1][member]point ex pointLaw HPointLaw).
   exists ex. split;[reflexivity|exact HP]. }
 assert(PPoint:source_zfr_provable M pointLaw).
 { apply(source_zfr_rec_exa_subset_successor M phi(succM M o)(succM M a)(succM M N)(succM M X)(zeroM M)
    totalG nonzero1 inj1 totality1 chart1 member ex pointLaw(succM M k));try rec_closed_bound;assumption. }
 assert(BFun:source_bounded M totalG k)by exact(source_bounded_monotone M totalG(zeroM M)k(source_rec_total_relation_closed M phi totalG BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M nonzero k)by exact(source_rec_nonzero_bounded M o N nonzero k BO BN HAF).
 assert(BAG:source_bounded M inj k)by exact(source_rec_injectivity_bounded M N inj k BN HAG).
 pose proof(source_rec_totality_bounded M N totality k BN HTotality)as BTotality.
 pose proof(source_rec_exa_subset_chart_bounded M phi o a N X chart k BP BO BA BN BX HChart)as BChart.
 apply(source_zfr_finite_telescope_all M[totalG;nonzero;inj;totality;chart][totalG;nonzero1;inj1;totality1;chart1]point closed pointLaw law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption.
 - exact BPoint.
 - repeat(constructor;[assumption|]). constructor.
 - exact HA.
 - exact HPointLaw.
 - exact HLaw.
 - exact PPoint.
Qed.
Print Assumptions source_zfr_rec_exa_subset_closed.
