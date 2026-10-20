(** Pure source proof of a condition followed by identity. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts
  SourcePropositionalTemplates SourceFunctionalityShells SourceDescriptorProvability SourceDescriptorClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_descriptor_conditional_identity M T condition body map result k :
  source_bounded M condition k ->source_bounded M body k ->
  sf_relation M SFImpl body body map ->sf_relation M SFImpl condition map result ->
  source_descriptor_provable M T result.
Proof.
  intros HC HB HM HR.
  assert(P:source_prop_program[](SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 1)))).
  { apply SPTII,SPTII,SPTCtx. now left. }
  set(rho:=fun i:nat=>match i with 0=>condition|_=>body end).
  assert(HRho:forall i,source_bounded M(rho i)k)by(intros[|i];unfold rho;assumption).
  assert(HGraph:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 1))))result).
  { unfold rho,source_prop_expression. functionality_graph. }
  apply source_descriptor_provable_from_empty.
  exact(source_prop_program_sound M[]_ P rho k(zeroM M)(zeroM M)(zeroM M)result HRho
    (context_bounded_empty M(zeroM M)(zeroM M)k)ltac:(intros a HA;destruct HA)HGraph).
Qed.
Print Assumptions source_descriptor_conditional_identity.
