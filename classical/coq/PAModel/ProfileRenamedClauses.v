(** A proof of one raw Collection profile supplies the renamed universal
    clauses needed by the quotient witness proof. No profile semantics is used. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NamedBinderFresh StableContextSupport
  ReplacementMatrixQuotation RawCollectionProfile RawClauseAlpha RawClauseHygiene
  BinaryMatrixRenaming MatrixClauseRenaming RawProfileGraphs.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem stable_raw_profile_renamed_clauses M cb cc cn phi eb ec en t a c base
    u0 v0 u1 v1 theta0 theta1 profile allcoverage allsupport :
  raw_clause_usable_name M eb ec en t a c base u0 ->
  raw_clause_usable_name M eb ec en t a c base v0 ->
  raw_clause_usable_name M eb ec en t a c base u1 ->
  raw_clause_usable_name M eb ec en t a c base v1 ->
  u0<>u1 -> u0<>v0 -> u0<>v1 -> v0<>u1 -> v0<>v1 -> u1<>v1 ->
  binary_matrix_quotation M phi eb ec en u0 v0 base t theta0 ->
  binary_matrix_quotation M phi eb ec en u1 v1 base t theta1 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  code_relation M (raw_clause_parameters M t a c u1 v1 theta1)
    (E_wal (CEvar 3) E_raw_coverage_clause) allcoverage ->
  code_relation M (raw_clause_parameters M t a c u1 v1 theta1)
    (E_wal (CEvar 4) E_raw_support_clause) allsupport ->
  stable_context_support M cb cc cn profile ->
  stable_context_support M cb cc cn allcoverage /\ stable_context_support M cb cc cn allsupport.
Proof.
  intros NU0 NV0 NU1 NV1 HUU HUV HUV' HVU' HVV HU'V' Q0 Q1 GP GC GS PP.
  destruct (raw_profile_parts_of_code M t a c u0 v0 theta0 profile GP)
    as [dom [coverage [support [allc [alls [both Parts]]]]]].
  pose proof (stable_raw_profile_parts M cb cc cn t a c u0 v0 theta0 profile dom coverage support allc alls both Parts PP)
    as [_ [PC PS]].
  destruct Parts as [GD [GC0 [GS0 [GAC [GAS [GB GAll]]]]]].
  assert (GAC0:code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_wal (CEvar 3) E_raw_coverage_clause) allc).
  { exact (proj2 (expression_universal_iff M (raw_clause_parameters M t a c u0 v0 theta0) (CEvar 3) E_raw_coverage_clause u0 coverage allc eq_refl GC0) GAC). }
  assert (GAS0:code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_wal (CEvar 4) E_raw_support_clause) alls).
  { exact (proj2 (expression_universal_iff M (raw_clause_parameters M t a c u0 v0 theta0) (CEvar 4) E_raw_support_clause v0 support alls eq_refl GS0) GAS). }
  split.
  - apply (stable_context_support_equivalent M cb cc cn allc allcoverage);[|exact PC].
    exact (quoted_raw_coverage_binders_alpha M phi eb ec en t a c base u0 v0 u1 v1 theta0 theta1 allc allcoverage
      NU0 NV0 NU1 NV1 HUU HUV HUV' HVU' HVV HU'V' Q0 Q1 GAC0 GC).
  - apply (stable_context_support_equivalent M cb cc cn alls allsupport);[|exact PS].
    exact (quoted_raw_support_binders_alpha M phi eb ec en t a c base u0 v0 u1 v1 theta0 theta1 alls allsupport
      NU0 NV0 NU1 NV1 HUU HUV HUV' HVU' HVV HU'V' Q0 Q1 GAS0 GS).
Qed.

Theorem renamed_raw_clause_binders_absent M phi eb ec en t a c base u v theta coverage support :
  coding_lt M u base -> coding_lt M v base -> u<>v ->
  binary_matrix_quotation M phi eb ec en u v base t theta ->
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_coverage_clause coverage ->
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_support_clause support ->
  named_binder_absent M coverage u /\ named_binder_absent M support v.
Proof.
  intros HU HV HUV HQ HC HS;split.
  - apply (raw_coverage_clause_binder_absent M t a c u v theta coverage u);[congruence| |exact HC].
    exact (binary_matrix_binder_absent M phi eb ec en u v base t theta u HQ HU).
  - apply (raw_support_clause_binder_absent M t a c u v theta support v HUV);[|exact HS].
    exact (binary_matrix_binder_absent M phi eb ec en u v base t theta v HQ HV).
Qed.

Print Assumptions stable_raw_profile_renamed_clauses.
Print Assumptions renamed_raw_clause_binders_absent.

