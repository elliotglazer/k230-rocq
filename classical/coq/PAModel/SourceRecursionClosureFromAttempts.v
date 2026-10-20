(** Obtain the predecessor witness from the actual successor clause of an attempt. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttemptStep SourceRecursionAttemptStepShell
 SourceRecursionClosureInputs SourceRecursionClosureTransition SourceRecursionNextIn SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_from_attempts M phi o a N f g z v w next Y A successor target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->coding_lt M next k ->coding_lt M Y k ->
 source_rec_closure_inputs M phi o a N f g z v w next Y A ->source_rec_successor M z next successor ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[successor])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BZ BV BW BNext BY HA HS HTarget HLaw.
 pose proof(source_rec_closure_inputs_bounded M phi o a N f g z v w next Y A k BP BO BA BN BF BG BZ BV BW BNext BY HA)as Bounds.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 pose proof(source_rec_successor_bounded M z next successor k BZ BNext HS)as BS.
 destruct(source_rec_transition_witness_total M phi g z w)as(transition&HTransition).
 destruct(source_finite_telescope_total M(A++[transition])target)as(use&HUse).
 pose proof(source_zfr_rec_closure_transition M phi o a N f g z v w next Y A transition target use k
  BP BO BA BN BF BG BZ BV BW BNext BY HA HTransition HTarget HUse)as PUse.
 destruct HA as(background&af&ag&mz&appf&appnext&mnext&chart&E&HBack&HAF&HAG&HMZ&HAppF&HAppNext&HMNext&HChart). subst A.
 apply(source_zfr_finite_rule M[use]((background++[af;ag;mz;appf;appnext;mnext;chart])++[successor])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BS].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PUse.
 - intros cb cc cn BC Laws Premises.
   assert(PT:source_full_prv M cb cc cn transition).
   { apply(source_full_rec_attempt_step M cb cc cn phi o a N g ag z next w mz successor appnext transition BP HAG HMZ HS HAppNext HTransition);
     apply Premises;rewrite !in_app_iff;cbn;tauto. }
   apply(source_full_finite_telescope_apply M((background++[af;ag;mz;appf;appnext;mnext;chart])++[transition])target use HUse cb cc cn).
   + apply Laws. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[apply Premises,in_or_app;now left|exact PT].
Qed.
Print Assumptions source_zfr_rec_closure_from_attempts.
