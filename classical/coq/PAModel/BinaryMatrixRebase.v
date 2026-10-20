(** Moving both source quotations of a binary matrix to a common fresh
    base preserves their numerical theorem, including nonstandard codes. *)
From PAModel Require Import Model FiniteCoding NumericalEquivalence NumericalEnvironments
  NumericalQuotation QuotationHygiene QuotationRebase ReplacementMatrixQuotation
  ReplacementMatrixCongruence.
Unset Implicit Arguments.

Theorem binary_matrix_quotation_rebase M phi eb ec en x y oldbase fresh domain f g :
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en fresh domain ->
  coding_lt M x oldbase -> coding_lt M y oldbase ->
  coding_lt M x fresh -> coding_lt M y fresh ->
  binary_matrix_quotation M phi eb ec en x y oldbase domain f ->
  binary_matrix_quotation M phi eb ec en x y fresh domain g -> numerical_equivalent M f g.
Proof.
  intros HO HN HX HY HX' HY' [yb [yc [yn [xb [xc [xn [CY [CX HF]]]]]]]] HG.
  destruct (numerical_quotation_total M phi xb xc xn fresh domain) as [v HV].
  assert (E:v=g).
  { apply (binary_matrix_quotation_functional M phi eb ec en x y fresh domain v g);[|exact HG].
    exists yb,yc,yn,xb,xc,xn;split;[exact CY|]. split;assumption. }
  subst v.
  apply (numerical_quotation_rebase_safe M phi xb xc xn oldbase fresh domain f g);[| |exact HF|exact HV].
  - split;[exact (proj1 HO)|].
    apply (replacement_environment_push_below M yb yc yn x xb xc xn oldbase);[|exact HX|exact CX].
    exact (replacement_environment_push_below M eb ec en y yb yc yn oldbase (proj2 HO) HY CY).
  - split;[exact (proj1 HN)|].
    apply (replacement_environment_push_below M yb yc yn x xb xc xn fresh);[|exact HX'|exact CX].
    exact (replacement_environment_push_below M eb ec en y yb yc yn fresh (proj2 HN) HY' CY).
Qed.

Print Assumptions binary_matrix_quotation_rebase.
