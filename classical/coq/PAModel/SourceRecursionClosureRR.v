(** A literal RR witness yields a next value in the same carrier. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionRangeRelation SourceRecursionClosureDomainInputs SourceRecursionClosureCarrierInputs
 SourceRecursionClosureOldAttempt SourceRecursionNextIn SourceRecursionRangeBackground SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_rr M phi o a N z v Y A rr target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M z k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_carrier_inputs M phi o a N Y A ->source_rec_rr M phi z v o a N rr ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[rr])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BZ BV BY HA HR HTarget HLaw.
 pose proof(source_rec_closure_carrier_inputs_bounded M phi o a N Y A k BP BO BA BN BY HA)as Bounds.
 pose proof(source_rec_rr_bounded M phi z v o a N rr k BP BZ BV BO BA BN HR)as BR.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HR as(mz&witness&HMZ&HW&HAnd).
 destruct HA as(background&chart&allExA&E&HBack&HChart&HAll). subst A.
 set(B:=background++[mz;chart;allExA]).
 assert(HB:source_rec_closure_domain_inputs M phi o a N z Y B)by(exists background,mz,chart,allExA;auto).
 destruct(source_finite_telescope_total M(B++[witness])target)as(oldUse&HOldUse).
 pose proof(source_zfr_rec_closure_old_attempt M phi o a N z v Y B witness target oldUse k BP BO BA BN BZ BV BY HB HW HTarget HOldUse)as POldUse.
 apply(source_zfr_finite_rule M[oldUse]((background++[chart;allExA])++[rr])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BR].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact POldUse.
 - intros cb cc cn BC Laws Premises.
   destruct(source_full_piece_conjunction_components M cb cc cn mz witness rr HAnd(Premises rr ltac:(rewrite !in_app_iff;cbn;tauto)))as[PMZ PW].
   apply(source_full_finite_telescope_apply M(B++[witness])target oldUse HOldUse cb cc cn).
   + apply Laws. now left.
   + intros x HX. unfold B in HX. rewrite !in_app_iff in HX. cbn in HX. destruct HX as[HX|[<-|[]]].
     * destruct HX as[HX|[<-|[<-|[<-|[]]]]];first[exact PMZ|apply Premises;rewrite !in_app_iff;cbn;tauto].
     * exact PW.
Qed.
Print Assumptions source_zfr_rec_closure_rr.
