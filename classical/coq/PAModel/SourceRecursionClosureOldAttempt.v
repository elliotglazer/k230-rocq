(** Eliminate the genuine old-attempt witness mapping the current index to its value. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionAttemptApp SourceRecursionClosureDomainInputs SourceRecursionClosureIndexInputs SourceRecursionClosureSuccessor
 SourceRecursionNextIn SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_old_attempt M phi o a N z v Y A witness target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M z k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_domain_inputs M phi o a N z Y A ->source_rec_attempt_app M phi z v o a N witness ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[witness])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BZ BV BY HA HW HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_closure_domain_inputs_bounded M phi o a N z Y A k BP BO BA BN BZ BY HA)as Bounds.
 pose proof(source_rec_attempt_app_bounded M phi z v o a N witness k BP BZ BV BO BA BN HW)as BW.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HW as(af&appf&body&HAF&HAppF&HBody&HEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx body witness k(or_intror eq_refl)HEx)BW)as BBody.
 destruct(source_rec_closure_domain_inputs_total M phi(s o)(s a)(s N)(s z)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_domain_inputs_shift M phi o a N z Y A AS BP HA HAS)as HS.
 destruct(source_rec_next_in_total M phi(s v)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_next_in_shift M phi v Y target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_next_in_bounded M phi(s v)(s Y)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct HAS as(background&mz&chart&allExA&E&HBack&HMZ&HChart&HAll). subst AS.
   set(B:=background++[af;mz;appf;chart;allExA]).
   assert(HB:source_rec_closure_index_inputs M phi(s o)(s a)(s N)(zeroM M)(s z)(s v)(s Y)B).
   { exists background,af,mz,appf,chart,allExA. split;[reflexivity|]. auto 10. }
   destruct(source_finite_telescope_total M B targetS)as(indexUse&HIndexUse).
   pose proof(source_zfr_rec_closure_successor M phi(s o)(s a)(s N)(zeroM M)(s z)(s v)(s Y)B targetS indexUse(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HB HTargetS HIndexUse)as PIndexUse.
   apply(source_zfr_finite_rule M[indexUse]((background++[mz;chart;allExA])++[body])targetS deep(s k));[|exact BTargetS|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A _ k HS Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PIndexUse.
   - intros cb cc cn BC Laws Premises.
     destruct(source_full_piece_conjunction_components M cb cc cn af appf body HBody(Premises body ltac:(rewrite !in_app_iff;cbn;tauto)))as[PAF PAppF].
     apply(source_full_finite_telescope_apply M B targetS indexUse HIndexUse cb cc cn).
     + apply Laws. now left.
     + intros x HX. unfold B in HX. apply in_app_or in HX. destruct HX as[HX|[<-|[<-|[<-|[<-|[<-|[]]]]]]];first[exact PAF|exact PAppF|apply Premises;rewrite !in_app_iff;cbn;tauto]. }
 exact(source_zfr_finite_telescope_exists M A AS body witness target targetS deep law k Bounds BW BTarget HS HEx STarget HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_closure_old_attempt.
