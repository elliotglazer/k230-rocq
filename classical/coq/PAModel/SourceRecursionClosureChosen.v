(** Eliminate the genuine App(next) value witness of a chosen next attempt. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopePermutation
 SourceRecursionPrimitiveRelations SourceRecursionAppExists SourceRecursionClosureInputs SourceRecursionClosureChosenInputs
 SourceRecursionClosureFromAttempts SourceRecursionNextIn SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_chosen M phi o a N f g z v next Y A some target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M v k ->coding_lt M next k ->coding_lt M Y k ->source_rec_closure_chosen_inputs M phi o a N f g z v next Y A ->
 source_rec_app_exists M g next some ->source_rec_next_in M phi v Y target ->source_finite_telescope M(A++[some])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BZ BV BNext BY HA HSome HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_closure_chosen_inputs_bounded M phi o a N f g z v next Y A k BP BO BA BN BF BG BZ BV BNext BY HA)as Bounds.
 pose proof(source_rec_app_exists_bounded M g next some k BG BNext HSome)as BSome.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HSome as(appnext&HAppNext&HEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx appnext some k(or_intror eq_refl)HEx)BSome)as BAppNext.
 destruct(source_rec_closure_chosen_inputs_total M phi(s o)(s a)(s N)(s f)(s g)(s z)(s v)(s next)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_chosen_inputs_shift M phi o a N f g z v next Y A AS BP HA HAS)as HS.
 destruct(source_rec_next_in_total M phi(s v)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_next_in_shift M phi v Y target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_next_in_bounded M phi(s v)(s Y)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[appnext])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct HAS as(background&af&ag&mz&appf&mnext&chart&successor&E&HBack&HAF&HAG&HMZ&HAppF&HMNext&HChart&HSuccessor). subst AS.
   set(B:=background++[af;ag;mz;appf;appnext;mnext;chart]).
   assert(HB:source_rec_closure_inputs M phi(s o)(s a)(s N)(s f)(s g)(s z)(s v)(zeroM M)(s next)(s Y)B).
   { exists background,af,ag,mz,appf,appnext,mnext,chart. split;[reflexivity|]. auto 10. }
   destruct(source_finite_telescope_total M(B++[successor])targetS)as(natural&HNatural).
   pose proof(source_zfr_rec_closure_from_attempts M phi(s o)(s a)(s N)(s f)(s g)(s z)(s v)(zeroM M)(s next)(s Y)B successor targetS natural(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HB HSuccessor HTargetS HNatural)as PNatural.
   apply(source_zfr_finite_telescope_inclusion M(B++[successor])((background++[af;ag;mz;appf;mnext;chart;successor])++[appnext])targetS natural deep(s k));[|exact BTargetS|exact HNatural|exact HDeep| |exact PNatural].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A _ k HS Bounds x HX)|exact BAppNext].
   - intros x HX. unfold B in HX. rewrite !in_app_iff in HX|-*. cbn in HX|-*. tauto. }
 exact(source_zfr_finite_telescope_exists M A AS appnext some target targetS deep law k Bounds BSome BTarget HS HEx STarget HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_closure_chosen.
