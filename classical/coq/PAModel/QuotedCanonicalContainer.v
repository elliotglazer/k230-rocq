(** The conditional raw-to-quotient Separation transfer, now at the atom
    allocation requested by the source image. Raw existence remains explicit. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalQuotation
  NumericalEnvironments QuotationHygiene SourceBounded FreshNames NumericalEquivalence
  SupportedQuotientEnvironments RawQuotientAtomCongruence TemplateFormulaFresh
  QuotedSameContainer SelectionMemberRebase.
Unset Implicit Arguments.

Theorem numerical_quoted_canonical_container M env T X A C W K P Q
    phi count eb ec en w z a c base wb wc wn zb zc zn k l t marker marker_name f g result :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t z w (succM M w) ->
  environment_cons M eb ec en w wb wc wn -> environment_cons M eb ec en z zb zc zn ->
  quotation_safe M wb wc wn k t -> quotation_safe M zb zc zn l t ->
  numerical_quotation M phi wb wc wn k t f -> numerical_quotation M phi zb zc zn l t g ->
  code_relation M env T t -> code_relation M env X z -> code_relation M env A a ->
  code_relation M env C c -> code_relation M env W w -> code_relation M env K base ->
  code_relation M env P f -> code_relation M env Q g ->
  quotient_pair_safe M t z a w -> quotient_pair_safe M t z a base ->
  quotient_pair_safe M t z c w -> quotient_pair_safe M t z c base ->
  formula_fresh M marker w -> formula_fresh M g w ->
  formula_fresh M marker z -> formula_fresh M marker c ->
  expression_fresh M env z (E_raw_selection_container T A C W P) ->
  code_relation M env
    (E_wim (E_wex C (E_raw_selection_container T A C W P))
      (E_wex C (E_selection_container_at T X A C K Q))) result ->
  numerical_implies M marker result.
Proof.
  intros HB HM HS HW HZ HK HL HF HG ET EX EA EC EW EK EP EQ HWa HKa HWc HKc HMw HQw HMz HMc HRFresh HResult.
  set (raw:=E_wex C (E_raw_selection_container T A C W P)).
  set (intermediate:=E_wex C (E_quotient_selection_container T X A C W Q)).
  set (canonical:=E_wex C (E_selection_container_at T X A C K Q)).
  destruct (code_relation_total M (E_wim raw intermediate) env) as [step EStep].
  pose proof (numerical_quoted_same_container M env T X A C W P Q phi count eb ec en w z c
    wb wc wn zb zc zn k l t marker marker_name f g step HB HM HS HW HZ HK HL HF HG
    ET EX EW EC EP EQ HMw HQw HMz HMc HRFresh EStep) as HFirst.
  assert (HRebase : expression_equivalent M env intermediate canonical).
  { exact (selection_container_rebase M env T X A C W K Q t z a c w base
      ET EX EA EC EW EK HWa HKa HWc HKc). }
  assert (HImplications : expression_equivalent M env
    (E_wim raw intermediate) (E_wim raw canonical)).
  { apply expression_equivalent_implication;[apply expression_equivalent_refl|exact HRebase]. }
  pose proof (proj1 (numerical_equivalent_expression M env (E_wim raw intermediate)
    (E_wim raw canonical) step result EStep HResult) HImplications) as HCodes.
  exact (numerical_implies_trans M marker step result HFirst (proj1 HCodes)).
Qed.

Print Assumptions numerical_quoted_canonical_container.
