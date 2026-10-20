(** A first actual WF Separation proof step for arbitrary internal matrices:
    the Separation equivalence implies that the new object is a subset. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition SPTIff a b := SPTAnd (SPTImpl a b) (SPTImpl b a).
Definition separation_subset_program := SPTImpl
  (SPTIff (SPTSlot 0) (SPTAnd (SPTSlot 1) (SPTSlot 2)))
  (SPTImpl (SPTSlot 0) (SPTSlot 1)).

Theorem separation_subset_program_checked : source_prop_program [] separation_subset_program.
Proof.
  unfold separation_subset_program,SPTIff. apply SPTII,SPTII.
  apply SPTCE1 with (b:=SPTSlot 2).
  apply SPTIE with (a:=SPTSlot 0).
  - apply SPTCE1 with (b:=SPTImpl (SPTAnd (SPTSlot 1) (SPTSlot 2)) (SPTSlot 0)).
    apply SPTCtx. cbn;auto.
  - apply SPTCtx. cbn;auto.
Qed.

Theorem numerical_source_separation_subset_projection M rho k b c n f :
  (forall i,source_bounded M (rho i) k) -> context_bounded M b c n k ->
  code_relation M rho (source_prop_expression separation_subset_program) f ->
  source_full_prv M b c n f.
Proof.
  intros HB HC HF. apply (source_prop_program_sound M [] separation_subset_program
    separation_subset_program_checked rho k b c n f HB HC);[|exact HF].
  intros a HA. contradiction.
Qed.

Print Assumptions separation_subset_program_checked.
Print Assumptions numerical_source_separation_subset_projection.
