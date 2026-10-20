(** Pointwise quotient Separation with the exact dmem outer syntax.
    The input is the raw guarded membership equivalence at a chosen fresh
    representative name. Source predicates are actual bounded quotations. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates
  NumericalProofs NumericalEnvironments NumericalQuotation QuotationHygiene
  SourceBounded FreshNames RawQuotientAtomCongruence SupportedQuotientEnvironments
  QuotientAtomTemplates QuotationPayloads NumericalEquivalence QuotientSeparationWitness
  QuotientMemberExpansion QuotedSeparationReversePoint.
Unset Implicit Arguments.

Definition E_raw_member_selection T A C W P :=
  E_wal W (E_selection_raw (E_wel T W) (E_wel W C) (E_wel W A) P).

Definition E_literal_member_selection T X A C W Q :=
  E_selection_iff (E_member_witness T X C W)
    (E_wa (E_member_witness T X A W) Q).

Theorem numerical_literal_member_selection M env T X A C W P Q
    phi count eb ec en w z wb wc wn zb zc zn k l t marker marker_name f g result :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t z w (succM M w) ->
  environment_cons M eb ec en w wb wc wn -> environment_cons M eb ec en z zb zc zn ->
  quotation_safe M wb wc wn k t -> quotation_safe M zb zc zn l t ->
  numerical_quotation M phi wb wc wn k t f -> numerical_quotation M phi zb zc zn l t g ->
  code_relation M env T t -> code_relation M env X z -> code_relation M env W w ->
  code_relation M env P f -> code_relation M env Q g ->
  formula_fresh M marker w -> formula_fresh M g w ->
  code_relation M env
    (E_wim (E_raw_member_selection T A C W P) (E_literal_member_selection T X A C W Q)) result ->
  numerical_implies M marker result.
Proof.
  intros HB HM HEqSafe HW HZ HK HL HF HG ET EX EW EP EQ HMfresh HQfresh HResult.
  set (E := code_subst (quotation_atom_parameters X W T (CEadd W (CEconst 1)) (CEconst 0))
    quotient_equal_template).
  destruct (code_relation_total M E env) as [eqcode EE].
  assert (HEq : quotation_atom M true z w t (succM M w) eqcode).
  { exact (proj1 (member_witness_equality_graph M env T X W t z w eqcode ET EX EW) EE). }
  exact (numerical_quoted_selection_point_reverse M env W (E_wel T W) (E_wel W C)
    (E_wel W A) E P Q phi count eb ec en w z wb wc wn zb zc zn k l t marker marker_name
    (succM M w) eqcode f g result HB HM HEqSafe HEq HW HZ HK HL HF HG EW EE EP EQ
    HMfresh HQfresh HResult).
Qed.

Print Assumptions numerical_literal_member_selection.
