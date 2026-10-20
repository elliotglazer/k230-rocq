(** Eliminate the next-attempt existential from actual uniform attempt existence. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionClosureChosenInputs SourceRecursionClosureNextInputs SourceRecursionClosureChosen
 SourceRecursionExistsAttempt SourceRecursionNextIn SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_next M phi o a N f z v next Y A exa target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->
 coding_lt M z k ->coding_lt M v k ->coding_lt M next k ->coding_lt M Y k ->source_rec_closure_next_inputs M phi o a N f z v next Y A ->
 source_rec_exa M phi next o a N exa ->source_rec_next_in M phi v Y target ->source_finite_telescope M(A++[exa])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BV BNext BY HA HExA HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_closure_next_inputs_bounded M phi o a N f z v next Y A k BP BO BA BN BF BZ BV BNext BY HA)as Bounds.
 pose proof(source_rec_exa_bounded M phi next o a N exa k BP BNext BO BA BN HExA)as BExA.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HExA as(ag&some&body&HAG&HSome&HBody&HEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx body exa k(or_intror eq_refl)HEx)BExA)as BBody.
 destruct(source_rec_closure_next_inputs_total M phi(s o)(s a)(s N)(s f)(s z)(s v)(s next)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_next_inputs_shift M phi o a N f z v next Y A AS BP HA HAS)as HS.
 destruct(source_rec_next_in_total M phi(s v)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_next_in_shift M phi v Y target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_next_in_bounded M phi(s v)(s Y)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct HAS as(background&af&mz&appf&mnext&chart&successor&E&HBack&HAF&HMZ&HAppF&HMNext&HChart&HSuccessor). subst AS.
   set(B:=background++[af;ag;mz;appf;mnext;chart;successor]).
   assert(HB:source_rec_closure_chosen_inputs M phi(s o)(s a)(s N)(s f)(zeroM M)(s z)(s v)(s next)(s Y)B).
   { exists background,af,ag,mz,appf,mnext,chart,successor. split;[reflexivity|]. auto 10. }
   destruct(source_finite_telescope_total M(B++[some])targetS)as(chosen&HChosen).
   pose proof(source_zfr_rec_closure_chosen M phi(s o)(s a)(s N)(s f)(zeroM M)(s z)(s v)(s next)(s Y)B some targetS chosen(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HB HSome HTargetS HChosen)as PChosen.
   apply(source_zfr_finite_rule M[chosen]((background++[af;mz;appf;mnext;chart;successor])++[body])targetS deep(s k));[|exact BTargetS|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A _ k HS Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PChosen.
   - intros cb cc cn BC Laws Premises.
     destruct(source_full_piece_conjunction_components M cb cc cn ag some body HBody(Premises body ltac:(rewrite !in_app_iff;cbn;tauto)))as[PAG PSome].
     apply(source_full_finite_telescope_apply M(B++[some])targetS chosen HChosen cb cc cn).
     + apply Laws. now left.
     + intros x HX. unfold B in HX. rewrite !in_app_iff in HX. cbn in HX. destruct HX as[HX|[<-|[]]].
       * destruct HX as[HX|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];first[exact PAG|apply Premises;rewrite !in_app_iff;cbn;tauto].
       * exact PSome. }
 exact(source_zfr_finite_telescope_exists M A AS body exa target targetS deep law k Bounds BExA BTarget HS HEx STarget HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_closure_next.
