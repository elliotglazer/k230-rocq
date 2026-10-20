(** The actual guarded implication argument for An minus (Rleft minus
    Rright). The carrier point is essential: no representation membership
    claim is made outside the assignment guard. Every slot may be an
    arbitrary internally coded source formula. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceUniversalMacro SourceFiniteTelescope
 NumericalSourceFull SourceDescriptorProvability SourceDescriptorClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition implication_difference_hypotheses :=
 [SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1));
  SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2));
  SPTImpl(SPTSlot 6)(SPTSlot 7);
  SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4));
  SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))].
Definition implication_difference_conclusion :=SPTImpl(SPTSlot 6)
 (SPTIff(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))).
Ltac id_ctx :=apply SPTCtx;cbn;auto 16.

Theorem implication_difference_representation_program :
 source_prop_program implication_difference_hypotheses implication_difference_conclusion.
Proof.
 unfold implication_difference_hypotheses,implication_difference_conclusion.
 apply SPTII,SPTCI.
 - apply SPTII,SPTII.
   apply(source_program_iff_left _ (SPTSlot 1)(SPTSlot 5)).
   + eapply SPTIE with(a:=SPTSlot 6);id_ctx.
   + eapply SPTIE;[exact(SPTPc _ (SPTSlot 1) SPTFalse)|]. apply SPTII,SPTExp.
     eapply SPTIE with(a:=SPTSlot 2).
     * apply SPTCE2 with(a:=SPTSlot 7).
       apply(source_program_iff_left _ (SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2)));id_ctx.
     * apply(source_program_iff_right _ (SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1))).
       -- id_ctx.
       -- apply SPTCI.
          ++ apply(source_program_iff_right _ (SPTSlot 0)(SPTSlot 4)).
             ** eapply SPTIE with(a:=SPTSlot 6);id_ctx.
             ** id_ctx.
          ++ id_ctx.
 - apply SPTII.
   apply(source_program_iff_right _ (SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2))).
   + id_ctx.
   + apply SPTCI.
     * eapply SPTIE with(a:=SPTSlot 6);id_ctx.
     * apply SPTII. eapply SPTIE with(a:=SPTSlot 1).
       -- apply SPTCE2 with(a:=SPTSlot 0).
          apply(source_program_iff_left _ (SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1)));id_ctx.
       -- apply(source_program_iff_right _ (SPTSlot 1)(SPTSlot 5)).
          ++ eapply SPTIE with(a:=SPTSlot 6);id_ctx.
          ++ eapply SPTIE with(a:=SPTSlot 4).
             ** id_ctx.
             ** apply(source_program_iff_left _ (SPTSlot 0)(SPTSlot 4)).
                --- eapply SPTIE with(a:=SPTSlot 6);id_ctx.
                --- apply SPTCE1 with(b:=SPTNot(SPTSlot 1)).
                    apply(source_program_iff_left _ (SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1)));id_ctx.
Qed.

Theorem source_descriptor_implication_difference_universal_macro M T rho k codes body all out :
 (forall i,source_bounded M(rho i)(succM M k)) ->
 source_universal_macro_graph M rho implication_difference_hypotheses codes ->
 code_relation M rho(source_prop_expression implication_difference_conclusion)body ->
 sf_relation M SFAll body(zeroM M)all ->source_finite_telescope M codes all out ->
 source_descriptor_provable M T out.
Proof.
 intros HB HG HBody HAll HT. apply source_descriptor_provable_from_empty.
 exact(source_empty_universal_macro M rho k implication_difference_hypotheses implication_difference_conclusion
  codes body all out HB implication_difference_representation_program HG HBody HAll HT).
Qed.
Print Assumptions implication_difference_representation_program.
Print Assumptions source_descriptor_implication_difference_universal_macro.
