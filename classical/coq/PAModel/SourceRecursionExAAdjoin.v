(** Eliminate the genuine adjoining-set existential in successor ExA. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopePermutation SourceFiniteTelescopeRemoveTheorem
 SourceRecursionPrimitiveRelations SourceRecursionSetOperations SourceRecursionSetOperationTransport SourceRecursionPrimitiveShifts
 SourceRecursionPrimitiveExistence SourceRecursionStructureGraphs SourceRecursionExAStepInputs SourceRecursionExtensionInputs SourceRecursionExtensionInputShift
 SourceRecursionExAExtensionPoint SourceRecursionExistsAttempt SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_exa_name_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_exa_name_bound].
Theorem source_zfr_rec_exa_with_pair M phi o a N f z next p w q A op target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->coding_lt M q k ->
 source_rec_exa_step_inputs M phi o a N f z next p w A ->source_rec_ordered_pair M next w q op ->source_rec_exa M phi next o a N target ->
 source_finite_telescope M(A++[op])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BNext BP' BW BQ HInputs HOp HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_exa_step_inputs_bounded M phi o a N f z next p w A k BP BO BA BN BF BZ BNext BP' BW HInputs)as Bounds.
 pose proof(source_rec_ordered_pair_bounded M next w q op k BNext BW BQ HOp)as BOp.
 pose proof(source_rec_exa_bounded M phi next o a N target k BP BNext BO BA BN HTarget)as BTarget.
 destruct(source_zfr_rec_adjoin_exists M f q)as(body&ex&HBody&HEx&PEx).
 pose proof(source_rec_adjoin_bounded M(s f)(s q)(zeroM M)body(s k) ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HBody)as BBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)BBody)as BEx.
 destruct(source_rec_exa_step_inputs_total M phi(s o)(s a)(s N)(s f)(s z)(s next)(s p)(s w))as(AS&HIS).
 pose proof(source_rec_exa_step_inputs_shift M phi o a N f z next p w A AS BP HInputs HIS)as HS.
 pose proof(source_finite_shifted_bounds M A AS k HS Bounds)as BoundsS.
 destruct(source_rec_ordered_pair_total M(s next)(s w)(s q))as(opS&HOpS).
 pose proof(source_rec_ordered_pair_shift M next w q op opS HOp HOpS)as SOp.
 pose proof(source_rec_ordered_pair_bounded M(s next)(s w)(s q)opS(s k) ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HOpS)as BOpS.
 destruct(source_rec_exa_total M phi(s next)(s o)(s a)(s N))as(targetS&HTargetS).
 pose proof(source_rec_exa_shift M phi next o a N target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_exa_bounded M phi(s next)(s o)(s a)(s N)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M((AS++[opS])++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct HIS as(nonzero&inj&att&mz&sz&appf&binary&E&HNZ&HI&HT&HMZ&HSZ&HAF&HG). subst AS.
   set(AE:=[inj;att;mz;sz;appf;body;opS;binary]).
   assert(HE:source_rec_extension_inputs M phi(s o)(s a)(s N)(s f)(s q)(zeroM M)(s z)(s next)(s p)(s w)AE).
   { exists inj,att,mz,sz,appf,body,opS,binary. split;[reflexivity|]. auto 10. }
   destruct(source_finite_telescope_total M(nonzero::AE)targetS)as(natural&HNatural).
   pose proof(source_zfr_rec_exa_extension_point M phi(s o)(s a)(s N)(s f)(s q)(zeroM M)(s z)(s next)(s p)(s w)
    nonzero AE targetS natural(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HNZ HE HTargetS HNatural)as PNatural.
   apply(source_zfr_finite_telescope_inclusion M(nonzero::AE)(([nonzero;inj;att;mz;sz;appf;binary]++[opS])++[body])targetS natural deep(s k));[|exact BTargetS|exact HNatural|exact HDeep| |exact PNatural].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[|exact BBody].
     apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(BoundsS x HX)|exact BOpS].
   - intros x HX. unfold AE in HX. cbn in HX|-*. tauto. }
 destruct(source_finite_telescope_total M((A++[op])++[ex])target)as(withEx&HWithEx).
 assert(PWithEx:source_zfr_provable M withEx).
 { apply(source_zfr_finite_telescope_exists M(A++[op])(AS++[opS])body ex target targetS deep withEx k).
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BOp].
   - exact BEx.
   - exact BTarget.
   - apply Forall2_app;[exact HS|]. constructor;[exact SOp|constructor].
   - exact HEx.
   - exact STarget.
   - exact HDeep.
   - exact HWithEx.
   - exact PDeep. }
 apply(source_zfr_finite_telescope_remove_theorem M(A++[op])ex target withEx law k);[|exact BTarget|exact HWithEx|exact HLaw|exact PEx|exact PWithEx].
 intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BOp].
Qed.
Print Assumptions source_zfr_rec_exa_with_pair.
