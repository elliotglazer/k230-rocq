(** Compile a checked propositional deduction under one actual source
    universal quantifier. Its slots remain arbitrary internal formulas. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalContextRenaming NumericalSourceFull
  SourcePropositionalTemplates SourceUniversalPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition source_universal_program_hypotheses M rho A b c n :=
  forall p, In p A -> forall body all,
    code_relation M rho (source_prop_expression p) body ->
    sf_relation M SFAll body (zeroM M) all -> source_full_prv M b c n all.

Theorem source_full_universal_program M A p :
  source_prop_program A p -> forall rho k b c n body all,
  (forall i, source_bounded M (rho i) (succM M k)) ->
  context_bounded M b c n k ->
  source_universal_program_hypotheses M rho A b c n ->
  code_relation M rho (source_prop_expression p) body ->
  sf_relation M SFAll body (zeroM M) all -> source_full_prv M b c n all.
Proof.
  intros Program rho k b c n body all HB HC HH HBody HAll.
  destruct (context_shift_total M b c n) as (u&v&HShift).
  apply (full_source_AllI M b c n body all u v).
  - exists k. split;[|exact HC].
    apply (proj2 (source_bounded_accept_unary M SFAll body all k
      (or_introl eq_refl) HAll)).
    exact (source_prop_template_bound M rho p (succM M k) HB body HBody).
  - apply (source_prop_program_sound M A p Program rho (succM M k) u v n body HB).
    + exact (context_shift_preserves_bound M b c n u v k HShift HC).
    + intros q HQ f HF.
      destruct (sf_relation_total M SFAll f (zeroM M)) as [af HAF].
      exact (source_full_all_shift M b c n f af u v HAF
        (HH q HQ f af HF HAF) HShift).
    + exact HBody.
  - exact HShift.
  - exact HAll.
Qed.

Print Assumptions source_full_universal_program.
