(** The literal RR relation is functional, with its genuine background hypotheses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttemptApp SourceRecursionRangeRelation SourceRecursionRangeWitnessEquality
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_rr_equality M phi o a N z v w funlaw totality induction member left right equal law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->
 source_rec_functionality M phi funlaw ->source_rec_totality M N totality ->source_rec_induction M o N induction ->sf_relation M SFMember o N member ->
 source_rec_rr M phi z v o a N left ->source_rec_rr M phi z w o a N right ->sf_relation M SFEqual v w equal ->
 source_finite_telescope M[funlaw;totality;induction;member;left;right]equal law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BZ BV BW HFun HT HI HM HL HR HE HLaw.
 pose proof(source_rec_rr_bounded M phi z v o a N left k BP BZ BV BO BA BN HL)as BL.
 pose proof(source_rec_rr_bounded M phi z w o a N right k BP BZ BW BO BA BN HR)as BR.
 pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
 pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
 pose proof(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k))as BFun.
 pose proof(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN))as BM.
 pose proof(proj2(source_bounded_accept_atom M SFEqual v w equal k(or_intror eq_refl)HE)(conj BV BW))as BE.
 destruct HL as(mz&wl&HMZ&HWL&HAndL). destruct HR as(mz'&wr&HMZ'&HWR&HAndR).
 destruct(source_finite_telescope_total M[funlaw;totality;induction;member;mz;wr;wl]equal)as(witnessLaw&HWitnessLaw).
 pose proof(source_zfr_rec_range_witness_equality M phi o a N z v w funlaw totality induction member mz wl wr equal witnessLaw k
  BP BO BA BN BZ BV BW HFun HT HI HM HMZ HWL HWR HE HWitnessLaw)as PWitnessLaw.
 apply(source_zfr_finite_rule M[witnessLaw][funlaw;totality;induction;member;left;right]equal law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BE.
 - exact HLaw.
 - intros x[<-|[]]. exact PWitnessLaw.
 - intros cb cc cn BC Laws Premises.
   destruct(source_full_piece_conjunction_components M cb cc cn mz wl left HAndL(Premises left ltac:(cbn;tauto)))as[PMZ PWL].
   destruct(source_full_piece_conjunction_components M cb cc cn mz' wr right HAndR(Premises right ltac:(cbn;tauto)))as[PMZ' PWR].
   apply(source_full_finite_telescope_apply M[funlaw;totality;induction;member;mz;wr;wl]equal witnessLaw HWitnessLaw cb cc cn).
   + apply Laws. now left.
   + intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];first[exact PMZ|exact PWL|exact PWR|apply Premises;cbn;tauto].
Qed.
Print Assumptions source_zfr_rec_rr_equality.
