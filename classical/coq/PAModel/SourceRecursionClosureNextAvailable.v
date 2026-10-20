(** Use actual all-index ExA to supply the next-attempt witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionClosureNextInputs SourceRecursionClosureNext
 SourceRecursionExistsAttempt SourceRecursionExAOn SourceRecursionExAOnUse SourceRecursionNextIn SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_next_available M phi o a N f z v next Y A allExA target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M v k ->coding_lt M next k ->coding_lt M Y k ->
 source_rec_closure_next_inputs M phi o a N f z v next Y A ->source_rec_exa_on M phi o a N allExA ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[allExA])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BV BNext BY HA HAll HTarget HLaw.
 pose proof(source_rec_closure_next_inputs_bounded M phi o a N f z v next Y A k BP BO BA BN BF BZ BV BNext BY HA)as Bounds.
 pose proof(source_rec_exa_on_bounded M phi o a N allExA k BP BO BA BN HAll)as BAll.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct(source_rec_exa_total M phi next o a N)as(exa&HExA).
 destruct(source_finite_telescope_total M(A++[exa])target)as(use&HUse).
 pose proof(source_zfr_rec_closure_next M phi o a N f z v next Y A exa target use k BP BO BA BN BF BZ BV BNext BY HA HExA HTarget HUse)as PUse.
 destruct HA as(background&af&mz&appf&mnext&chart&successor&E&HBack&HAF&HMZ&HAppF&HMNext&HChart&HS). subst A.
 apply(source_zfr_finite_rule M[use]((background++[af;mz;appf;mnext;chart;successor])++[allExA])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BAll].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PUse.
 - intros cb cc cn BC Laws Premises.
   assert(PE:source_full_prv M cb cc cn exa).
   { apply(source_full_rec_exa_on_use M cb cc cn phi o a N allExA next mnext exa BP HAll HMNext HExA);
     apply Premises;rewrite !in_app_iff;cbn;tauto. }
   apply(source_full_finite_telescope_apply M((background++[af;mz;appf;mnext;chart;successor])++[exa])target use HUse cb cc cn).
   + apply Laws. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[apply Premises,in_or_app;now left|exact PE].
Qed.
Print Assumptions source_zfr_rec_closure_next_available.
