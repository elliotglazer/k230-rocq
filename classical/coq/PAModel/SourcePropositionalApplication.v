(** Apply a fixed, kernel-checked propositional program directly to actual
    numerical premise proofs, with arbitrary internal formula holes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem source_prop_program_apply M a d :
  source_prop_program nil (SPTImpl a d) ->
  forall rho k b c n left right,
    (forall i,source_bounded M (rho i) k) -> context_bounded M b c n k ->
    code_relation M rho (source_prop_expression a) left ->
    code_relation M rho (source_prop_expression d) right ->
    source_full_prv M b c n left -> source_full_prv M b c n right.
Proof.
  intros Program rho k b c n left right HB HC HL HR HP.
  destruct (sf_relation_total M SFImpl left right) as [imp HI].
  apply (full_source_IE M b c n left right imp).
  - exists k. split;[|exact HC]. exact (source_prop_template_bound M rho d k HB right HR).
  - apply (source_prop_program_sound M nil (SPTImpl a d) Program rho k b c n imp HB HC).
    + intros x HX. destruct HX.
    + exact (source_prop_template_join M rho SFImpl a d left right imp HL HR HI).
  - exact HP.
  - exact HI.
Qed.

Print Assumptions source_prop_program_apply.
