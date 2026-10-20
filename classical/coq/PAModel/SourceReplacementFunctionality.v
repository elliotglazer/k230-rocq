(** Actual functionality cleanup for the exact guarded Replacement matrix,
    with the real RepA/RepB renaming and constructor graphs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalContextRenaming NumericalRenaming
  SourceQuantifierRules SourceRelativizationBounds NumericalSourceFull
  SourceRelativeSchemaInputs SchemaRenamingDescriptors SourcePropositionalTemplates
  SourceReplacementPropositional SourceImplicationAllShift SourceReplacementThreeQuantifiers
  SourceReplacementGuardRenaming SourceFunctionalityShells.
Unset Implicit Arguments.

Theorem source_full_guarded_replacement_functionality M b c n k domain rphi matrix ra rb ma mb f g :
  context_bounded M b c n k -> source_bounded M domain (code_numeral M 1) ->
  source_bounded M ra (succM M (succM M (succM M k))) ->
  source_bounded M rb (succM M (succM M (succM M k))) ->
  relative_replacement_matrix M domain rphi matrix ->
  schema_renaming M RepA matrix ma -> schema_renaming M RepB matrix mb ->
  schema_renaming M RepA rphi ra -> schema_renaming M RepB rphi rb ->
  source_relative_functionality_graph M domain ra rb f ->
  source_functionality_graph M ma mb g -> source_full_prv M b c n f ->
  source_full_prv M b c n g.
Proof.
  intros HC HD HA HB HM HMA HMB HRA HRB HF HG PF.
  destruct (numerical_renaming_total M domain (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [d1 HS1].
  destruct (numerical_renaming_total M d1 (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [d2 HS2].
  destruct (source_replacement_guarded_pair_shapes M domain d1 d2 rphi matrix ra rb ma mb
    HD HS1 HS2 HM HMA HMB HRA HRB) as [ga [gb [HGA [HMA' [HGB HMB']]]]].
  destruct (sf_relation_total M SFEqual (code_numeral M 1) (zeroM M)) as [eq HE].
  destruct (source_relative_functionality_shell M domain ra rb eq f HE HF)
    as (rhs&point&g2&p1&g1&p0&g0&HR&HP&HG2&HQ2&HG1&HQ1&HG0&HQ0).
  destruct (source_functionality_shell M ma mb eq g HE HG)
    as (trhs&target&t1&t2&HTR&HT&HT1&HT2&HT3).
  set (rho:=fun i:nat=>match i with 0=>d2 | 1=>d1 | 2=>domain | 3=>ra | 4=>rb | _=>eq end).
  assert (HEBound:source_bounded M eq (succM M (succM M (succM M k)))).
  { apply (proj2 (source_bounded_accept_atom M SFEqual (code_numeral M 1) (zeroM M) eq
      (succM M (succM M (succM M k))) (or_intror eq_refl) HE)). split.
    - apply coding_lt_succ_cancel,coding_zero_lt_succ.
    - apply coding_zero_lt_succ. }
  assert (HSlots:forall i,source_bounded M (rho i) (succM M (succM M (succM M k)))).
  { intros [|[|[|[|[|i]]]]];cbn [rho].
    - apply (source_shift_bound M d1 d2 (succM M (succM M k)));[|exact HS2].
      exact (source_shift_bound M domain d1 (succM M k)
        (sr_domain_bound_succ M domain k HD) HS1).
    - exact (source_shift_bound M domain d1 (succM M (succM M k))
        (sr_domain_bound_succ M domain (succM M k) HD) HS1).
    - exact (sr_domain_bound_succ M domain (succM M (succM M k)) HD).
    - exact HA.
    - exact HB.
    - exact HEBound. }
  assert (HPoint:code_relation M rho (source_prop_expression replacement_point) point).
  { unfold replacement_point. cbn [source_prop_expression]. functionality_graph. }
  assert (HTarget:code_relation M rho (source_prop_expression replacement_unguarded_point) target).
  { unfold replacement_unguarded_point,replacement_guarded_left,replacement_guarded_right.
    cbn [source_prop_expression]. functionality_graph. }
  exact (source_full_replacement_three_quantifiers M rho k b c n
    point g2 p1 g1 p0 g0 f target t1 t2 g
    HC HSlots HD HS1 HS2 HPoint HG2 HQ2 HG1 HQ1 HG0 HQ0 HTarget HT1 HT2 HT3 PF).
Qed.

Print Assumptions source_full_guarded_replacement_functionality.
