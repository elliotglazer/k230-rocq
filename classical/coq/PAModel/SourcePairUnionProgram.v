(** The disjunction representation point, with arbitrary internal formulas.
    The quantified profile and two child points are genuine source premises. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceUniversalMacro SourceFiniteTelescope
 NumericalSourceFull SourceDescriptorProvability SourceDescriptorClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition pair_union_profile_template:=SPTIff(SPTSlot 3)(SPTOr(SPTSlot 0)(SPTSlot 1)).
Definition pair_union_left_template:=SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4)).
Definition pair_union_right_template:=SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5)).
Definition pair_union_hypotheses:=[pair_union_profile_template;pair_union_left_template;pair_union_right_template].
Definition pair_union_conclusion:=SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 3)(SPTOr(SPTSlot 4)(SPTSlot 5))).
Ltac pu_ctx:=apply SPTCtx;cbn;auto 12.
Theorem pair_union_representation_program:source_prop_program pair_union_hypotheses pair_union_conclusion.
Proof.
 unfold pair_union_hypotheses,pair_union_profile_template,pair_union_left_template,pair_union_right_template,pair_union_conclusion.
 apply SPTII,SPTCI.
 - apply SPTII. eapply SPTDE with(a:=SPTSlot 0)(b:=SPTSlot 1).
   + apply(source_program_iff_left _ (SPTSlot 3)(SPTOr(SPTSlot 0)(SPTSlot 1)));pu_ctx.
   + apply SPTDI1. apply(source_program_iff_left _ (SPTSlot 0)(SPTSlot 4)).
     * eapply SPTIE with(a:=SPTSlot 6);pu_ctx.
     * pu_ctx.
   + apply SPTDI2. apply(source_program_iff_left _ (SPTSlot 1)(SPTSlot 5)).
     * eapply SPTIE with(a:=SPTSlot 6);pu_ctx.
     * pu_ctx.
 - apply SPTII. apply(source_program_iff_right _ (SPTSlot 3)(SPTOr(SPTSlot 0)(SPTSlot 1))).
   + pu_ctx.
   + eapply SPTDE with(a:=SPTSlot 4)(b:=SPTSlot 5);[pu_ctx| |].
     * apply SPTDI1. apply(source_program_iff_right _ (SPTSlot 0)(SPTSlot 4)).
       -- eapply SPTIE with(a:=SPTSlot 6);pu_ctx.
       -- pu_ctx.
     * apply SPTDI2. apply(source_program_iff_right _ (SPTSlot 1)(SPTSlot 5)).
       -- eapply SPTIE with(a:=SPTSlot 6);pu_ctx.
       -- pu_ctx.
Qed.
Theorem source_descriptor_pair_union_universal_macro M T rho k codes body all out:
 (forall i,source_bounded M(rho i)(succM M k)) ->
 source_universal_macro_graph M rho pair_union_hypotheses codes ->
 code_relation M rho(source_prop_expression pair_union_conclusion)body ->sf_relation M SFAll body(zeroM M)all ->
 source_finite_telescope M codes all out ->source_descriptor_provable M T out.
Proof.
 intros HB HG HBody HAll HT. apply source_descriptor_provable_from_empty.
 exact(source_empty_universal_macro M rho k pair_union_hypotheses pair_union_conclusion codes body all out
  HB pair_union_representation_program HG HBody HAll HT).
Qed.
Print Assumptions pair_union_representation_program.
Print Assumptions source_descriptor_pair_union_universal_macro.
