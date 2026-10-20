(** Rebase the matrix in a derived copy of the raw profile before moving
    its binders. The original low-base profile can remain in the context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalEquivalence
  StableContextSupport QuotationHygiene RawCollectionProfile RawClauseAlpha RawProfileMatrixEquivalence
  ReplacementMatrixQuotation MatrixClauseRenaming ProfileRenamedClauses BinaryMatrixRebase.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem stable_raw_profile_rebased_clauses M cb cc cn phi eb ec en t a c oldbase base
    u0 v0 u1 v1 theta0 theta1 profile allcoverage allsupport :
  quotation_safe M eb ec en oldbase t -> quotation_safe M eb ec en base t ->
  coding_lt M u0 oldbase -> coding_lt M v0 oldbase ->
  raw_clause_usable_name M eb ec en t a c base u0 ->
  raw_clause_usable_name M eb ec en t a c base v0 ->
  raw_clause_usable_name M eb ec en t a c base u1 ->
  raw_clause_usable_name M eb ec en t a c base v1 ->
  u0<>u1 -> u0<>v0 -> u0<>v1 -> v0<>u1 -> v0<>v1 -> u1<>v1 ->
  binary_matrix_quotation M phi eb ec en u0 v0 oldbase t theta0 ->
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
  intros HOld HBase HU0 HV0 NU0 NV0 NU1 NV1 HUU HUV HUV' HVU' HVV HU'V' Q0 Q1 GP GC GS PP.
  destruct (binary_matrix_total M phi eb ec en u0 v0 base t) as [thetaM QM].
  destruct (code_relation_total M
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5))
    (raw_clause_parameters M t a c u0 v0 thetaM)) as [profileM GPM].
  assert (PMP:stable_context_support M cb cc cn profileM).
  { apply (stable_context_support_equivalent M cb cc cn profile profileM);[|exact PP].
    apply (raw_profile_matrix_equivalence M t a c u0 v0 theta0 thetaM profile profileM);try assumption.
    apply (binary_matrix_quotation_rebase M phi eb ec en u0 v0 oldbase base t theta0 thetaM);try assumption.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 NU0))))).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 NV0))))). }
  exact (stable_raw_profile_renamed_clauses M cb cc cn phi eb ec en t a c base
    u0 v0 u1 v1 thetaM theta1 profileM allcoverage allsupport
    NU0 NV0 NU1 NV1 HUU HUV HUV' HVU' HVV HU'V' QM Q1 GPM GC GS PMP).
Qed.

Print Assumptions stable_raw_profile_rebased_clauses.
