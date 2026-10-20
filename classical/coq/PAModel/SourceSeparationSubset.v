(** Uniform quantified subset extraction from an actual Separation profile.
    The predicate matrix is an arbitrary internal source-formula code. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded NumericalContexts NumericalContextRenaming
  NumericalSourceFull SourcePropositionalTemplates SourceSeparationPropositional
  SourceUniversalPropositional.
Unset Implicit Arguments.

Definition separation_point_template :=
  SPTIff (SPTSlot 0) (SPTAnd (SPTSlot 1) (SPTSlot 2)).

Theorem source_full_separation_subset_projection M b c n k left right theta
    body allbody subset allsubset :
  context_bounded M b c n k ->
  source_bounded M left (succM M k) -> source_bounded M right (succM M k) ->
  source_bounded M theta (succM M k) ->
  code_relation M (schema_env3 left right theta) (source_prop_expression separation_point_template) body ->
  sf_relation M SFAll body (zeroM M) allbody -> sf_relation M SFImpl left right subset ->
  sf_relation M SFAll subset (zeroM M) allsubset -> source_full_prv M b c n allbody ->
  source_full_prv M b c n allsubset.
Proof.
  intros HC HL HR HT HBody HAllBody HSubset HAllSubset PBody.
  destruct (context_shift_total M b c n) as [u [v HShift]].
  destruct (sf_relation_total M SFImpl body subset) as [projection HProjection].
  apply (source_full_universal_map M b c n body subset allbody allsubset projection u v).
  - exists k. split;[|exact HC].
    apply (proj2 (source_bounded_accept_unary M SFAll subset allsubset k
      (or_introl eq_refl) HAllSubset)).
    apply (proj2 (source_bounded_accept_binary M SFImpl left right subset (succM M k)
      (or_intror (or_intror eq_refl)) HSubset)). split;assumption.
  - exact HAllBody.
  - exact HAllSubset.
  - exact HProjection.
  - exact HShift.
  - exact PBody.
  - apply (numerical_source_separation_subset_projection M (schema_env3 left right theta)
      (succM M k) u v n projection).
    + intros [|[|i]];[exact HL|exact HR|exact HT].
    + exact (context_shift_preserves_bound M b c n u v k HShift HC).
    + apply (source_prop_template_join M (schema_env3 left right theta) SFImpl
        separation_point_template (SPTImpl (SPTSlot 0) (SPTSlot 1)) body subset projection).
      * exact HBody.
      * exact (source_prop_template_join M (schema_env3 left right theta) SFImpl
          (SPTSlot 0) (SPTSlot 1) left right subset eq_refl eq_refl HSubset).
      * exact HProjection.
Qed.

Print Assumptions source_full_separation_subset_projection.
