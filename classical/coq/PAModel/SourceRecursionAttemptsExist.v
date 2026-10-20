(** Uniform existence of an attempt and value at every internal recursion index.
    The ExA Separation witness, its SInd induction and every quantifier
    are discharged in the numerical source proof calculus. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceClosedShift
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport SourceRecursionAtomicShift
 SourceRecursionTotalRelation SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceRecursionInductionShift
 SourceRecursionInductionTransport SourceRecursionExASubset SourceRecursionExASeparation SourceRecursionExASubsetTransport
 SourceRecursionExAOn SourceRecursionExAInduction SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_agree_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_agree_bound].
Theorem source_zfr_rec_attempts_exist M phi o a N totalG nonzero inj totality induction member target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->
 source_rec_total_relation M phi totalG ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->
 source_rec_totality M N totality ->source_rec_induction M o N induction ->sf_relation M SFMember o N member ->
 source_rec_exa_on M phi o a N target ->source_finite_telescope M[totalG;nonzero;inj;totality;induction;member]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN HFun HAF HAG HT HI HM HTarget HLaw.
 destruct(source_zfr_rec_exa_subset_exists M phi o a N k BP BO BA BN)as(ex&body&HChart&HEx&PEx).
 destruct(source_rec_nonzero_total M(succM M o)(succM M N))as(nonzero1&HAF1).
 destruct(source_rec_injectivity_total M(succM M N))as(inj1&HAG1).
 destruct(source_rec_totality_total M(succM M N))as(totality1&HT1).
 destruct(source_rec_induction_total M(succM M o)(succM M N))as(induction1&HI1).
 destruct(sf_relation_total M SFMember(succM M o)(succM M N))as(member1&HM1).
 destruct(source_rec_exa_on_total M phi(succM M o)(succM M a)(succM M N))as(target1&HTarget1).
 pose proof(source_closed_shift_self M totalG(source_rec_total_relation_closed M phi totalG BP HFun))as SFun.
 pose proof(source_rec_nonzero_shift M o N nonzero nonzero1 HAF HAF1)as SAF.
 pose proof(source_rec_injectivity_shift M N inj inj1 HAG HAG1)as SAG.
 pose proof(source_rec_totality_shift M N totality totality1 HT HT1)as ST.
 pose proof(source_rec_induction_shift M o N induction induction1 HI HI1)as SI.
 pose proof(source_rec_member_shift M o N member member1 HM HM1)as SM.
 pose proof(source_rec_exa_on_shift M phi o a N target target1 BP HTarget HTarget1)as STarget.
 destruct(source_finite_telescope_total M[totalG;nonzero1;inj1;totality1;induction1;member1;body]target1)as(branchLaw&HBranchLaw).
 assert(PBranch:source_zfr_provable M branchLaw).
 { apply(source_zfr_rec_exa_induction M phi(succM M o)(succM M a)(succM M N)(zeroM M)
   totalG nonzero1 inj1 totality1 induction1 member1 body target1 branchLaw(succM M k));try rec_agree_bound;assumption. }
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HAF)as BAF.
 pose proof(source_rec_injectivity_bounded M N inj k BN HAG)as BAG.
 pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
 pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
 assert(BFun:source_bounded M totalG k)by exact(source_bounded_monotone M totalG(zeroM M)k(source_rec_total_relation_closed M phi totalG BP HFun)(coding_zero_lt_succ M k)).
 assert(BM:source_bounded M member k)by exact(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN)).
 pose proof(source_rec_exa_on_bounded M phi o a N target k BP BO BA BN HTarget)as BTarget.
 assert(BEx:source_bounded M ex k).
 { apply(proj2(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)).
   exact(source_rec_exa_subset_chart_bounded M phi(succM M o)(succM M a)(succM M N)(zeroM M)body(succM M k)BP
    (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)(coding_zero_lt_succ M k)HChart). }
 destruct(source_finite_telescope_total M[totalG;nonzero;inj;totality;induction;member;ex]target)as(exLaw&HExLaw).
 assert(PExLaw:source_zfr_provable M exLaw).
 { apply(source_zfr_finite_telescope_exists M[totalG;nonzero;inj;totality;induction;member][totalG;nonzero1;inj1;totality1;induction1;member1]
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
 apply(source_zfr_finite_rule M[ex;exLaw][totalG;nonzero;inj;totality;induction;member]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   apply(source_full_finite_telescope_apply M[totalG;nonzero;inj;totality;induction;member;ex]target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
     all:first[apply Premises;cbn;tauto|apply Laws;now left].
Qed.
Print Assumptions source_zfr_rec_attempts_exist.
