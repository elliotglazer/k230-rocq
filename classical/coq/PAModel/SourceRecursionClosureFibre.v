(** Eliminate the last domain-index witness, then obtain its fibre from range membership. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionRangeFibre SourceRecursionRangeChartRules SourceRecursionClosureCarrierInputs SourceRecursionClosureRR
 SourceRecursionNextIn SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_fibre M phi o a N v Y A fibre target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_carrier_inputs M phi o a N Y A ->source_rec_range_fibre M phi o a N v fibre ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[fibre])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BV BY HA HF HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_closure_carrier_inputs_bounded M phi o a N Y A k BP BO BA BN BY HA)as Bounds.
 pose proof(source_rec_range_fibre_bounded M phi o a N v fibre k BP BO BA BN BV HF)as BFibre.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HF as(member&rr&body&HM&HR&HBody&HEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx body fibre k(or_intror eq_refl)HEx)BFibre)as BBody.
 destruct(source_rec_closure_carrier_inputs_total M phi(s o)(s a)(s N)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_carrier_inputs_shift M phi o a N Y A AS BP HA HAS)as HS.
 destruct(source_rec_next_in_total M phi(s v)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_next_in_shift M phi v Y target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_next_in_bounded M phi(s v)(s Y)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct(source_finite_telescope_total M(AS++[rr])targetS)as(rrUse&HRRUse).
   pose proof(source_zfr_rec_closure_rr M phi(s o)(s a)(s N)(zeroM M)(s v)(s Y)AS rr targetS rrUse(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    HAS HR HTargetS HRRUse)as PRRUse.
   apply(source_zfr_finite_rule M[rrUse](AS++[body])targetS deep(s k));[|exact BTargetS|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A AS k HS Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PRRUse.
   - intros cb cc cn BC Laws Premises.
     pose proof(proj2(source_full_piece_conjunction_components M cb cc cn member rr body HBody(Premises body ltac:(rewrite in_app_iff;cbn;tauto))))as PRR.
     apply(source_full_finite_telescope_apply M(AS++[rr])targetS rrUse HRRUse cb cc cn).
     + apply Laws. now left.
     + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[apply Premises,in_or_app;now left|exact PRR]. }
 exact(source_zfr_finite_telescope_exists M A AS body fibre target targetS deep law k Bounds BFibre BTarget HS HEx STarget HDeep HLaw PDeep).
Qed.
Theorem source_zfr_rec_closure_member M phi o a N v Y A member target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_carrier_inputs M phi o a N Y A ->sf_relation M SFMember v Y member ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[member])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BV BY HA HM HTarget HLaw.
 pose proof(source_rec_closure_carrier_inputs_bounded M phi o a N Y A k BP BO BA BN BY HA)as Bounds.
 pose proof(proj2(source_bounded_accept_atom M SFMember v Y member k(or_introl eq_refl)HM)(conj BV BY))as BM.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct(source_rec_range_fibre_total M phi o a N v)as(fibre&HF).
 destruct(source_finite_telescope_total M(A++[fibre])target)as(fibreUse&HFibreUse).
 pose proof(source_zfr_rec_closure_fibre M phi o a N v Y A fibre target fibreUse k BP BO BA BN BV BY HA HF HTarget HFibreUse)as PFibreUse.
 destruct HA as(background&chart&allExA&E&HBack&HChart&HAll). subst A.
 apply(source_zfr_finite_rule M[fibreUse]((background++[chart;allExA])++[member])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BM].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PFibreUse.
 - intros cb cc cn BC Laws Premises.
   assert(PFibre:source_full_prv M cb cc cn fibre).
   { apply(source_full_rec_range_chart_out M cb cc cn phi o a N Y v chart member fibre BP HChart HM HF);
     apply Premises;rewrite !in_app_iff;cbn;tauto. }
   apply(source_full_finite_telescope_apply M((background++[chart;allExA])++[fibre])target fibreUse HFibreUse cb cc cn).
   + apply Laws. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[apply Premises,in_or_app;now left|exact PFibre].
Qed.
Print Assumptions source_zfr_rec_closure_fibre.
Print Assumptions source_zfr_rec_closure_member.
