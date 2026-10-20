(** The actual finite propositional argument for R1 minus (R1 minus R2).
    All seven slots may be arbitrary internally coded source formulas. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull SourcePropositionalTemplates SourceUniversalPrograms.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition SPTIff p q :=SPTAnd(SPTImpl p q)(SPTImpl q p).
Definition SPTNot p :=SPTImpl p SPTFalse.
Definition SPTDifference x y :=SPTAnd x(SPTNot y).
Lemma source_program_iff_left A p q :source_prop_program A(SPTIff p q) ->
 source_prop_program A p ->source_prop_program A q.
Proof. intros H P. eapply SPTIE;[exact(SPTCE1 A(SPTImpl p q)(SPTImpl q p) H)|exact P]. Qed.
Lemma source_program_iff_right A p q :source_prop_program A(SPTIff p q) ->
 source_prop_program A q ->source_prop_program A p.
Proof. intros H P. eapply SPTIE;[exact(SPTCE2 A(SPTImpl p q)(SPTImpl q p) H)|exact P]. Qed.
Ltac rep_sp_context :=apply SPTCtx;cbn;auto 12.
Definition double_difference_hypotheses :=
 [SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1));
  SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2));
  SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4));
  SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))].
Definition double_difference_conclusion :=SPTImpl(SPTSlot 6)
 (SPTIff(SPTSlot 3)(SPTAnd(SPTSlot 4)(SPTSlot 5))).
Theorem double_difference_representation_program :
 source_prop_program double_difference_hypotheses double_difference_conclusion.
Proof.
 unfold double_difference_hypotheses,double_difference_conclusion.
 apply SPTII,SPTCI.
 - apply SPTII,SPTCI.
   + apply(source_program_iff_left _ (SPTSlot 0)(SPTSlot 4)).
     * eapply SPTIE with(a:=SPTSlot 6);rep_sp_context.
     * apply SPTCE1 with(b:=SPTNot(SPTSlot 2)).
       apply(source_program_iff_left _ (SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2)));rep_sp_context.
   + apply(source_program_iff_left _ (SPTSlot 1)(SPTSlot 5)).
     * eapply SPTIE with(a:=SPTSlot 6);rep_sp_context.
     * eapply SPTIE;[exact(SPTPc _ (SPTSlot 1) SPTFalse)|]. apply SPTII,SPTExp.
       eapply SPTIE with(a:=SPTSlot 2).
       -- apply SPTCE2 with(a:=SPTSlot 0).
          apply(source_program_iff_left _ (SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2)));rep_sp_context.
       -- apply(source_program_iff_right _ (SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1))).
          ++ rep_sp_context.
          ++ apply SPTCI.
             ** apply SPTCE1 with(b:=SPTNot(SPTSlot 2)).
                apply(source_program_iff_left _ (SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2)));rep_sp_context.
             ** rep_sp_context.
 - apply SPTII.
   apply(source_program_iff_right _ (SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2))).
   + rep_sp_context.
   + apply SPTCI.
     * apply(source_program_iff_right _ (SPTSlot 0)(SPTSlot 4)).
       -- eapply SPTIE with(a:=SPTSlot 6);rep_sp_context.
       -- apply SPTCE1 with(b:=SPTSlot 5). rep_sp_context.
     * apply SPTII. eapply SPTIE with(a:=SPTSlot 1).
       -- apply SPTCE2 with(a:=SPTSlot 0).
          apply(source_program_iff_left _ (SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1)));rep_sp_context.
       -- apply(source_program_iff_right _ (SPTSlot 1)(SPTSlot 5)).
          ++ eapply SPTIE with(a:=SPTSlot 6);rep_sp_context.
          ++ apply SPTCE2 with(a:=SPTSlot 4). rep_sp_context.
Qed.
Theorem source_full_double_difference_representation M rho k b c n body all :
 (forall i,source_bounded M(rho i)(succM M k)) ->context_bounded M b c n k ->
 source_universal_program_hypotheses M rho double_difference_hypotheses b c n ->
 code_relation M rho(source_prop_expression double_difference_conclusion) body ->
 sf_relation M SFAll body(zeroM M) all ->source_full_prv M b c n all.
Proof.
 exact(source_full_universal_program M double_difference_hypotheses double_difference_conclusion
  double_difference_representation_program rho k b c n body all).
Qed.
Print Assumptions double_difference_representation_program.
Print Assumptions source_full_double_difference_representation.



