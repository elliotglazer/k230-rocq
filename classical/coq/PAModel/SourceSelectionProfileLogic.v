(** Finite source logic converting the literal Op5 profile through the
    guarded SC correctness statement. The arbitrary matrix is a code hole. *)
From PAModel Require Import Model CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition selection_profile_raw:=SPTIff(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 2)).
Definition selection_profile_guard:=SPTImpl(SPTSlot 1)(SPTIff(SPTSlot 2)(SPTSlot 3)).
Definition selection_profile_result:=SPTIff(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 3)).
Ltac slp_ctx:=apply SPTCtx;cbn;auto 12.
Lemma selection_profile_program:source_prop_program
 [selection_profile_raw;selection_profile_guard]selection_profile_result.
Proof.
 unfold selection_profile_raw,selection_profile_guard,selection_profile_result,SPTIff.
 apply SPTCI;apply SPTII.
 - assert(P:source_prop_program
    [SPTSlot 0;SPTAnd(SPTImpl(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 2)))
      (SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 2))(SPTSlot 0));
     SPTImpl(SPTSlot 1)(SPTAnd(SPTImpl(SPTSlot 2)(SPTSlot 3))(SPTImpl(SPTSlot 3)(SPTSlot 2)))]
    (SPTAnd(SPTSlot 1)(SPTSlot 2))).
   { eapply SPTIE with(a:=SPTSlot 0);[|slp_ctx].
     apply SPTCE1 with(b:=SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 2))(SPTSlot 0));slp_ctx. }
   apply SPTCI.
   + apply SPTCE1 with(b:=SPTSlot 2);exact P.
   + eapply SPTIE with(a:=SPTSlot 2);[|apply SPTCE2 with(a:=SPTSlot 1);exact P].
     apply SPTCE1 with(b:=SPTImpl(SPTSlot 3)(SPTSlot 2)).
     eapply SPTIE with(a:=SPTSlot 1);[slp_ctx|apply SPTCE1 with(b:=SPTSlot 2);exact P].
 - eapply SPTIE with(a:=SPTAnd(SPTSlot 1)(SPTSlot 2)).
   + apply SPTCE2 with(a:=SPTImpl(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 2)));slp_ctx.
   + apply SPTCI.
     * apply SPTCE1 with(b:=SPTSlot 3);slp_ctx.
     * eapply SPTIE with(a:=SPTSlot 3);[|apply SPTCE2 with(a:=SPTSlot 1);slp_ctx].
       apply SPTCE2 with(a:=SPTImpl(SPTSlot 2)(SPTSlot 3)).
       eapply SPTIE with(a:=SPTSlot 1);[slp_ctx|apply SPTCE1 with(b:=SPTSlot 3);slp_ctx].
Qed.
Theorem source_full_selection_profile_logic M gb gc gn values raw guard result k:
 (forall i,source_bounded M(values i)k) ->context_bounded M gb gc gn k ->
 code_relation M values(source_prop_expression selection_profile_raw)raw ->
 code_relation M values(source_prop_expression selection_profile_guard)guard ->
 code_relation M values(source_prop_expression selection_profile_result)result ->
 source_full_prv M gb gc gn raw ->source_full_prv M gb gc gn guard ->source_full_prv M gb gc gn result.
Proof.
 intros HB BC HRaw HGuard HResult PRaw PGuard.
 apply(source_prop_program_sound M _ _ selection_profile_program values k gb gc gn result HB BC).
 - intros p[<-|[<-|[]]]f HF.
   + assert(E:f=raw)by(eapply code_relation_functional;eassumption). now subst f.
   + assert(E:f=guard)by(eapply code_relation_functional;eassumption). now subst f.
 - exact HResult.
Qed.
Print Assumptions selection_profile_program.
Print Assumptions source_full_selection_profile_logic.
