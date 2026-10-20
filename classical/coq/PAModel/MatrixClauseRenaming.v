(** Both raw Collection binders can be moved to fresh witness names.
    All capture conditions follow from the actual matrix quotation. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NamedBinderFresh NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalQuotation
  QuotationBinderFresh ReplacementMatrixQuotation RawCollectionProfile RawClauseAlpha
  RawClauseHygiene RawClauseFullFresh RawInnerAlpha BinaryMatrixRenaming BinaryMatrixFresh.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition raw_clause_usable_name M eb ec en t a c base name :=
  name<>zeroM M /\ t<>name /\ a<>name /\ c<>name /\ coding_lt M name base /\
  environment_avoids_name M eb ec en name.

Lemma binary_matrix_total M phi eb ec en x y base t :
  exists theta,binary_matrix_quotation M phi eb ec en x y base t theta.
Proof.
  destruct (environment_cons_total M eb ec en y) as [yb [yc [yn CY]]].
  destruct (environment_cons_total M yb yc yn x) as [xb [xc [xn CX]]].
  destruct (numerical_quotation_total M phi xb xc xn base t) as [theta HQ].
  exists theta,yb,yc,yn,xb,xc,xn;auto.
Qed.

Lemma binary_matrix_binder_absent M phi eb ec en x y base t theta name :
  binary_matrix_quotation M phi eb ec en x y base t theta -> coding_lt M name base ->
  named_binder_absent M theta name.
Proof.
  intros [yb [yc [yn [xb [xc [xn [CY [CX HQ]]]]]]]] H.
  exact (numerical_quotation_binder_fresh M phi xb xc xn base t theta name HQ H).
Qed.

Theorem quoted_raw_support_binders_alpha M phi eb ec en t a c base u0 v0 u1 v1 theta0 theta1 all0 all1 :
  raw_clause_usable_name M eb ec en t a c base u0 ->
  raw_clause_usable_name M eb ec en t a c base v0 ->
  raw_clause_usable_name M eb ec en t a c base u1 ->
  raw_clause_usable_name M eb ec en t a c base v1 ->
  u0<>u1 -> u0<>v0 -> u0<>v1 -> v0<>u1 -> v0<>v1 -> u1<>v1 ->
  binary_matrix_quotation M phi eb ec en u0 v0 base t theta0 ->
  binary_matrix_quotation M phi eb ec en u1 v1 base t theta1 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_wal (CEvar 4) E_raw_support_clause) all0 ->
  code_relation M (raw_clause_parameters M t a c u1 v1 theta1)
    (E_wal (CEvar 4) E_raw_support_clause) all1 -> numerical_equivalent M all0 all1.
Proof.
  intros [HU0 [HTU0 [HAU0 [HCU0 [HU0B EU0]]]]]
    [HV0 [HTV0 [HAV0 [HCV0 [HV0B EV0]]]]]
    [HU1 [HTU1 [HAU1 [HCU1 [HU1B EU1]]]]]
    [HV1 [HTV1 [HAV1 [HCV1 [HV1B EV1]]]]]
    HUU HUV HUV' HVU' HVV HU'V' Q0 Q1 G0 G1.
  destruct (binary_matrix_total M phi eb ec en u0 v1 base t) as [thetaM QM].
  destruct (code_relation_total M E_raw_support_clause (raw_clause_parameters M t a c u0 v0 theta0)) as [body0 B0].
  destruct (code_relation_total M E_raw_support_clause (raw_clause_parameters M t a c u0 v1 thetaM)) as [bodyM BM].
  destruct (code_relation_total M (E_wal (CEvar 4) E_raw_support_clause)
    (raw_clause_parameters M t a c u0 v1 thetaM)) as [allM GM].
  apply (numerical_equivalent_trans M all0 allM all1).
  - apply (raw_support_clause_outer_alpha M t a c u0 v0 v1 theta0 thetaM body0 bodyM all0 allM);
      try assumption.
    + apply (raw_support_clause_binder_absent M t a c u0 v0 theta0 body0 v0 HUV);[|exact B0].
      exact (binary_matrix_binder_absent M phi eb ec en u0 v0 base t theta0 v0 Q0 HV0B).
    + apply (raw_support_expression_fresh M (raw_clause_parameters M t a c u0 v0 theta0)
        v1 (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5));try assumption.
      * now intros ? ->.
      * now intros ? ->.
      * now intros ? ->.
      * now intros ? ->.
      * now intros ? ->.
      * intros ? ->. exact (binary_matrix_formula_fresh M phi eb ec en u0 v0 base t theta0 v1
          Q0 HV1B HV1 ltac:(congruence) HUV' HVV EV1).
    + exact (binary_matrix_output_rename M phi eb ec en u0 v0 v1 base t theta0 thetaM
        HV0 HTV0 HUV HV0B HV1B EV0 Q0 QM).
    + exact (proj1 (expression_universal_iff M (raw_clause_parameters M t a c u0 v0 theta0)
        (CEvar 4) E_raw_support_clause v0 body0 all0 eq_refl B0) G0).
    + exact (proj1 (expression_universal_iff M (raw_clause_parameters M t a c u0 v1 thetaM)
        (CEvar 4) E_raw_support_clause v1 bodyM allM eq_refl BM) GM).
  - apply (raw_support_inner_alpha M t a c u0 u1 v1 thetaM theta1 allM all1);try assumption.
    + exact (binary_matrix_binder_absent M phi eb ec en u0 v1 base t thetaM u0 QM HU0B).
    + exact (binary_matrix_formula_fresh M phi eb ec en u0 v1 base t thetaM u1 QM HU1B HU1
        ltac:(congruence) HUU ltac:(congruence) EU1).
    + exact (binary_matrix_input_rename M phi eb ec en u0 u1 v1 base t thetaM theta1
        HU0 HTU0 ltac:(congruence) HU0B HU1B EU0 QM Q1).
Qed.

Print Assumptions binary_matrix_total.
Print Assumptions binary_matrix_binder_absent.
Print Assumptions quoted_raw_support_binders_alpha.


Theorem quoted_raw_coverage_binders_alpha M phi eb ec en t a c base u0 v0 u1 v1 theta0 theta1 all0 all1 :
  raw_clause_usable_name M eb ec en t a c base u0 ->
  raw_clause_usable_name M eb ec en t a c base v0 ->
  raw_clause_usable_name M eb ec en t a c base u1 ->
  raw_clause_usable_name M eb ec en t a c base v1 ->
  u0<>u1 -> u0<>v0 -> u0<>v1 -> v0<>u1 -> v0<>v1 -> u1<>v1 ->
  binary_matrix_quotation M phi eb ec en u0 v0 base t theta0 ->
  binary_matrix_quotation M phi eb ec en u1 v1 base t theta1 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_wal (CEvar 3) E_raw_coverage_clause) all0 ->
  code_relation M (raw_clause_parameters M t a c u1 v1 theta1)
    (E_wal (CEvar 3) E_raw_coverage_clause) all1 -> numerical_equivalent M all0 all1.
Proof.
  intros [HU0 [HTU0 [HAU0 [HCU0 [HU0B EU0]]]]]
    [HV0 [HTV0 [HAV0 [HCV0 [HV0B EV0]]]]]
    [HU1 [HTU1 [HAU1 [HCU1 [HU1B EU1]]]]]
    [HV1 [HTV1 [HAV1 [HCV1 [HV1B EV1]]]]]
    HUU HUV HUV' HVU' HVV HU'V' Q0 Q1 G0 G1.
  destruct (binary_matrix_total M phi eb ec en u1 v0 base t) as [thetaM QM].
  destruct (code_relation_total M E_raw_coverage_clause (raw_clause_parameters M t a c u0 v0 theta0)) as [body0 B0].
  destruct (code_relation_total M E_raw_coverage_clause (raw_clause_parameters M t a c u1 v0 thetaM)) as [bodyM BM].
  destruct (code_relation_total M (E_wal (CEvar 3) E_raw_coverage_clause)
    (raw_clause_parameters M t a c u1 v0 thetaM)) as [allM GM].
  apply (numerical_equivalent_trans M all0 allM all1).
  - apply (raw_coverage_clause_outer_alpha M t a c u0 u1 v0 theta0 thetaM body0 bodyM all0 allM);
      try assumption;try congruence.
    + apply (raw_coverage_clause_binder_absent M t a c u0 v0 theta0 body0 u0);[congruence| |exact B0].
      exact (binary_matrix_binder_absent M phi eb ec en u0 v0 base t theta0 u0 Q0 HU0B).
    + apply (raw_coverage_expression_fresh M (raw_clause_parameters M t a c u0 v0 theta0)
        u1 (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5));try assumption.
      * now intros ? ->.
      * now intros ? ->.
      * now intros ? ->.
      * now intros ? ->.
      * now intros ? ->.
      * intros ? ->. exact (binary_matrix_formula_fresh M phi eb ec en u0 v0 base t theta0 u1
          Q0 HU1B HU1 ltac:(congruence) HUU HVU' EU1).
    + exact (binary_matrix_input_rename M phi eb ec en u0 u1 v0 base t theta0 thetaM
        HU0 HTU0 ltac:(congruence) HU0B HU1B EU0 Q0 QM).
    + exact (proj1 (expression_universal_iff M (raw_clause_parameters M t a c u0 v0 theta0)
        (CEvar 3) E_raw_coverage_clause u0 body0 all0 eq_refl B0) G0).
    + exact (proj1 (expression_universal_iff M (raw_clause_parameters M t a c u1 v0 thetaM)
        (CEvar 3) E_raw_coverage_clause u1 bodyM allM eq_refl BM) GM).
  - apply (raw_coverage_inner_alpha M t a c u1 v0 v1 thetaM theta1 allM all1);try assumption.
    + exact (binary_matrix_binder_absent M phi eb ec en u1 v0 base t thetaM v0 QM HV0B).
    + exact (binary_matrix_formula_fresh M phi eb ec en u1 v0 base t thetaM v1 QM HV1B HV1
        ltac:(congruence) HU'V' HVV EV1).
    + exact (binary_matrix_output_rename M phi eb ec en u1 v0 v1 base t thetaM theta1
        HV0 HTV0 ltac:(congruence) HV0B HV1B EV0 QM Q1).
Qed.

Print Assumptions quoted_raw_coverage_binders_alpha.

