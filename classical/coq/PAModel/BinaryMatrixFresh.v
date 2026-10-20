(** Names excluded from the parameter environment and below the local
    allocation base are absent from the full binary-matrix quotation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions FreshNames NumericalEnvironments
  QuotationFormulaFresh ReplacementMatrixQuotation BinaryMatrixRenaming.
Unset Implicit Arguments.

Theorem binary_matrix_formula_fresh M phi eb ec en x y base domain result name :
  binary_matrix_quotation M phi eb ec en x y base domain result ->
  coding_lt M name base -> name<>zeroM M -> name<>domain -> x<>name -> y<>name ->
  environment_avoids_name M eb ec en name -> formula_fresh M result name.
Proof.
  intros [yb [yc [yn [xb [xc [xn [CY [CX HQ]]]]]]]] HN H0 HT HX HY HA.
  apply (numerical_quotation_formula_fresh M phi xb xc xn base domain result name HQ HN H0 HT).
  apply (quotation_environment_avoids_cons M yb yc yn x xb xc xn name);[|exact HX|exact CX].
  apply (quotation_environment_avoids_cons M eb ec en y yb yc yn name);[exact HA|exact HY|exact CY].
Qed.

Print Assumptions binary_matrix_formula_fresh.
