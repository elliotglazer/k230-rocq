(** Freshness conditions for same-container Separation. The first lemma
    proves freshness of a quotation at a different selected input; the
    second checks the entire raw-container assumption used in generalization. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalEnvironments
  NumericalQuotation QuotationFormulaFresh FreshNames TemplateFormulaFresh
  QuotientSeparationWitness LiteralMemberSeparationPoint.
Unset Implicit Arguments.

Theorem quoted_unary_avoiding_fresh M phi eb ec en selected mb mc mn base t q y :
  environment_cons M eb ec en selected mb mc mn ->
  numerical_quotation M phi mb mc mn base t q ->
  coding_lt M y base -> y<>zeroM M -> y<>t -> selected<>y ->
  quotation_environment_avoids M eb ec en y -> formula_fresh M q y.
Proof.
  intros HC HQ HY HZero HT HSelected HEnv.
  apply (numerical_quotation_formula_fresh M phi mb mc mn base t q y HQ HY HZero HT).
  exact (quotation_environment_avoids_cons M eb ec en selected mb mc mn y HEnv HSelected HC).
Qed.

Lemma selection_iff_fresh M env y P Q :
  y<>zeroM M -> expression_fresh M env y P -> expression_fresh M env y Q ->
  expression_fresh M env y (E_selection_iff P Q).
Proof.
  intros HZero HP HQ. unfold E_selection_iff.
  apply expression_fresh_conjunction;[exact HZero| |];
    apply expression_fresh_implication;assumption.
Qed.

Theorem raw_member_selection_body_fresh M env y T A C W P :
  y<>zeroM M ->
  expression_name_avoids M env y T -> expression_name_avoids M env y A ->
  expression_name_avoids M env y C -> expression_name_avoids M env y W ->
  expression_fresh M env y P ->
  expression_fresh M env y
    (E_wa (E_wel T C) (E_raw_member_selection T A C W P)).
Proof.
  intros HZero HT HA HC HW HP.
  apply expression_fresh_conjunction;[exact HZero| |].
  - apply expression_fresh_atom;[now left|exact HT|exact HC].
  - unfold E_raw_member_selection,E_selection_raw.
    apply expression_fresh_universal;[exact HW|].
    apply expression_fresh_implication.
    + apply expression_fresh_atom;[now left|exact HT|exact HW].
    + apply selection_iff_fresh;[exact HZero| |].
      * apply expression_fresh_atom;[now left|exact HW|exact HC].
      * apply expression_fresh_conjunction;[exact HZero| |exact HP].
        apply expression_fresh_atom;[now left|exact HW|exact HA].
Qed.

Print Assumptions quoted_unary_avoiding_fresh.
Print Assumptions raw_member_selection_body_fresh.
