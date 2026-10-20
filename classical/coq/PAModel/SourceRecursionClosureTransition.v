(** Eliminate the actual predecessor-value witness in the final recursion-closure argument. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionAttemptStepShell SourceRecursionValuePairs SourceRecursionClosureInputs SourceRecursionClosureValues
 SourceRecursionNextIn SourceRecursionBinaryInstance SourceRecursionRangeBackground SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_transition M phi o a N f g z v w next Y A transition target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->coding_lt M next k ->coding_lt M Y k ->
 source_rec_closure_inputs M phi o a N f g z v w next Y A ->source_rec_transition_witness M phi g z w transition ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[transition])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BZ BV BW BNext BY HA HTransition HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_closure_inputs_bounded M phi o a N f g z v w next Y A k BP BO BA BN BF BG BZ BV BW BNext BY HA)as Bounds.
 pose proof(source_rec_transition_witness_bounded M phi g z w transition k BP BG BZ BW HTransition)as BTransition.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HTransition as(appg&before&body&HAppG&HBefore&HBody&HEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx body transition k(or_intror eq_refl)HEx)BTransition)as BBody.
 destruct(source_rec_closure_inputs_total M phi(s o)(s a)(s N)(s f)(s g)(s z)(s v)(s w)(s next)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_inputs_shift M phi o a N f g z v w next Y A AS BP HA HAS)as HS.
 destruct(source_rec_next_in_total M phi(s v)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_next_in_shift M phi v Y target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_next_in_bounded M phi(s v)(s Y)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct HAS as(background&af&ag&mz&appf&appnext&mnext&chart&E&HBack&HAF&HAG&HMZ&HAppF&HAppNext&HMNext&HChart). subst AS.
   destruct HBack as(funlaw&totality&induction&member&EBack&HFun&HT&HI&HM). subst background.
   destruct(source_rec_binary_total M phi(s v)(s w))as(after&HAfter).
   destruct(sf_relation_total M SFMember(s w)(s Y))as(resultMember&HResultMember).
   destruct(sf_relation_total M SFAnd after resultMember)as(pair&HPair).
   destruct(source_finite_telescope_total M[funlaw;totality;induction;member;af;ag;mz;appf;appg;before;appnext;mnext;chart]pair)as(values&HValues).
   pose proof(source_zfr_rec_closure_values M phi(s o)(s a)(s N)(s f)(s g)(s z)(s v)(zeroM M)(s w)(s next)(s Y)
    funlaw totality induction member af ag mz appf appg before appnext mnext chart after resultMember pair values(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    HFun HT HI HM HAF HAG HMZ HAppF HAppG HBefore HAppNext HMNext HChart HAfter HResultMember HPair HValues)as PValues.
   apply(source_zfr_finite_rule M[values](([funlaw;totality;induction;member]++[af;ag;mz;appf;appnext;mnext;chart])++[body])targetS deep(s k));[|exact BTargetS|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A _ k HS Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PValues.
   - intros cb cc cn BC Laws Premises.
     assert(PBody:source_full_prv M cb cc cn body)by(apply Premises,in_or_app;right;now left).
     destruct(source_full_piece_conjunction_components M cb cc cn appg before body HBody PBody)as[PAppG PBefore].
     assert(PPair:source_full_prv M cb cc cn pair).
     { apply(source_full_finite_telescope_apply M[funlaw;totality;induction;member;af;ag;mz;appf;appg;before;appnext;mnext;chart]pair values HValues cb cc cn).
       - apply Laws. now left.
       - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];first[exact PAppG|exact PBefore|apply Premises,in_or_app;left;cbn;tauto]. }
     destruct(source_full_piece_conjunction_components M cb cc cn after resultMember pair HPair PPair)as[PAfter PResultMember].
     exact(source_full_rec_next_in_intro M cb cc cn phi(s v)(s Y)(s w)after resultMember targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
      BC HAfter HResultMember HTargetS PAfter PResultMember). }
 exact(source_zfr_finite_telescope_exists M A AS body transition target targetS deep law k Bounds BTransition BTarget HS HEx STarget HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_closure_transition.
