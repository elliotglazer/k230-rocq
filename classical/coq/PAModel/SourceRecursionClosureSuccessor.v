(** Eliminate the genuine successor-in-N witness and obtain it from actual STot. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceQuantifierRules SourceDerivedRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionClosureIndexInputs SourceRecursionClosureNextInputs SourceRecursionClosureNextAvailable
 SourceRecursionSuccessorIn SourceRecursionInductionShells SourceRecursionRangeBackground SourceRecursionNextIn SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_successor_exists M phi o a N f z v Y A exN target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_index_inputs M phi o a N f z v Y A ->source_rec_successor_in M z N exN ->source_rec_next_in M phi v Y target ->
 source_finite_telescope M(A++[exN])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BV BY HA HExN HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_closure_index_inputs_bounded M phi o a N f z v Y A k BP BO BA BN BF BZ BV BY HA)as Bounds.
 pose proof(source_rec_successor_in_bounded M z N exN k BZ BN HExN)as BExN.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct HExN as(successor&mnext&body&HSucc&HMNext&HBody&HEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx body exN k(or_intror eq_refl)HEx)BExN)as BBody.
 destruct(source_rec_closure_index_inputs_total M phi(s o)(s a)(s N)(s f)(s z)(s v)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_index_inputs_shift M phi o a N f z v Y A AS BP HA HAS)as HS.
 destruct(source_rec_next_in_total M phi(s v)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_next_in_shift M phi v Y target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_next_in_bounded M phi(s v)(s Y)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct HAS as(background&af&mz&appf&chart&allExA&E&HBack&HAF&HMZ&HAppF&HChart&HAll). subst AS.
   set(B:=background++[af;mz;appf;mnext;chart;successor]).
   assert(HB:source_rec_closure_next_inputs M phi(s o)(s a)(s N)(s f)(s z)(s v)(zeroM M)(s Y)B).
   { exists background,af,mz,appf,mnext,chart,successor. split;[reflexivity|]. auto 10. }
   destruct(source_finite_telescope_total M(B++[allExA])targetS)as(nextUse&HNextUse).
   pose proof(source_zfr_rec_closure_next_available M phi(s o)(s a)(s N)(s f)(s z)(s v)(zeroM M)(s Y)B allExA targetS nextUse(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HB HAll HTargetS HNextUse)as PNextUse.
   apply(source_zfr_finite_rule M[nextUse]((background++[af;mz;appf;chart;allExA])++[body])targetS deep(s k));[|exact BTargetS|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A _ k HS Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PNextUse.
   - intros cb cc cn BC Laws Premises.
     destruct(source_full_piece_conjunction_components M cb cc cn successor mnext body HBody(Premises body ltac:(rewrite !in_app_iff;cbn;tauto)))as[PSucc PMNext].
     apply(source_full_finite_telescope_apply M(B++[allExA])targetS nextUse HNextUse cb cc cn).
     + apply Laws. now left.
     + intros x HX. unfold B in HX. rewrite !in_app_iff in HX. cbn in HX. destruct HX as[HX|[<-|[]]].
       * destruct HX as[HX|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];first[exact PSucc|exact PMNext|apply Premises;rewrite !in_app_iff;cbn;tauto].
       * apply Premises. rewrite !in_app_iff. cbn. tauto. }
 exact(source_zfr_finite_telescope_exists M A AS body exN target targetS deep law k Bounds BExN BTarget HS HEx STarget HDeep HLaw PDeep).
Qed.
Theorem source_zfr_rec_closure_successor M phi o a N f z v Y A target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_index_inputs M phi o a N f z v Y A ->source_rec_next_in M phi v Y target ->source_finite_telescope M A target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BV BY HA HTarget HLaw.
 pose proof(source_rec_closure_index_inputs_bounded M phi o a N f z v Y A k BP BO BA BN BF BZ BV BY HA)as Bounds.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HTarget)as BTarget.
 destruct(source_zfr_rec_totality_use_total M N z)as(totality'&mz'&exN&tail&totalLaw&HT'&HMZ'&HExN&HTail&HTotalLaw&PTotalLaw).
 destruct(source_finite_telescope_total M(A++[exN])target)as(exLaw&HExLaw).
 pose proof(source_zfr_rec_closure_successor_exists M phi o a N f z v Y A exN target exLaw k BP BO BA BN BF BZ BV BY HA HExN HTarget HExLaw)as PExLaw.
 destruct HA as(background&af&mz&appf&chart&allExA&E&HBack&HAF&HMZ&HAppF&HChart&HAll). subst A.
 destruct HBack as(funlaw&totality&induction&member&EBack&HFun&HT&HI&HM). subst background.
 pose proof(code_relation_functional M _ _ totality' totality HT' HT)as E. subst totality'.
 pose proof(sf_relation_functional M SFMember z N mz' mz HMZ' HMZ)as E. subst mz'.
 apply(source_zfr_finite_rule M[totalLaw;exLaw]([funlaw;totality;induction;member]++[af;mz;appf;chart;allExA])target law k Bounds BTarget HLaw).
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   pose proof(source_full_modus_ponens M cb cc cn totality tail totalLaw HTotalLaw(Laws totalLaw(or_introl eq_refl))(Premises totality ltac:(cbn;tauto)))as PTail.
   pose proof(source_full_modus_ponens M cb cc cn mz exN tail HTail PTail(Premises mz ltac:(cbn;tauto)))as PExN.
   apply(source_full_finite_telescope_apply M(([funlaw;totality;induction;member]++[af;mz;appf;chart;allExA])++[exN])target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Premises x HX)|exact PExN].
Qed.
Print Assumptions source_zfr_rec_closure_successor_exists.
Print Assumptions source_zfr_rec_closure_successor.
