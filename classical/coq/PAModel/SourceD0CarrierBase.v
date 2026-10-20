(** Actual D0 base for carrier equality transport. Its two insertions are
    syntactically identical, so no equality rule on an arbitrary matrix is used. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
  SourceFiniteCutoffShift SourceD0Recipe SourceD0CarrierSyntax SourceHierarchySyntax
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceConditionalIdentity.
Unset Implicit Arguments.
Theorem source_zfr_d0_carrier_base M domain level phi d0 before after condition map result k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M phi(succM M k) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_d0_recipe M domain level phi d0 ->source_cutoff_shift M 2 d0 before ->source_cutoff_shift M 1 d0 after ->
  sf_relation M SFEqual(code_numeral M 1)(code_numeral M 2)condition ->
  sf_relation M SFImpl before after map ->sf_relation M SFImpl condition map result ->source_zfr_provable M result.
Proof.
  intros HD HL HB HLevel HG HBefore HAfter HEq HMap HResult.
  pose proof(source_d0_carrier_insertions_equal M domain level phi d0 before after k HD HB HLevel HG HBefore HAfter)as E. subst after.
  pose proof(source_d0_recipe_bounded M domain level phi d0 k HD HL HB HG)as BD0.
  pose proof(source_cutoff_shift_bounded M 2 d0 before k BD0 HBefore)as BBefore.
  assert(BCondition:source_bounded M condition(succM M(succM M(succM M k)))).
  { apply(proj2(source_bounded_accept_atom M SFEqual(code_numeral M 1)(code_numeral M 2)condition _ (or_intror eq_refl)HEq)).
    split;[apply coding_lt_succ_cancel,coding_zero_lt_succ|apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ]. }
  apply(proj1(source_zfr_descriptor_provable M result)).
  exact(source_descriptor_conditional_identity M ZFRSourceDescriptor condition before map result
    (succM M(succM M(succM M k)))BCondition BBefore HMap HResult).
Qed.
Print Assumptions source_zfr_d0_carrier_base.
