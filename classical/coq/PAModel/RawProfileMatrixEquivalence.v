(** The raw Collection profile respects proved equivalence of its matrix.
    This permits rebasing the quoted source matrix before witness renaming. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalEquivalence
  ProofTemplates RawCollectionProfile RawClauseAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma raw_support_expression_equivalent M rho T A C U V theta theta' :
  expression_equivalent M rho theta theta' ->
  expression_equivalent M rho (E_raw_collection_support T A C U V theta)
    (E_raw_collection_support T A C U V theta').
Proof.
  intro HE;unfold E_raw_collection_support.
  apply expression_equivalent_implication;[apply expression_equivalent_refl|].
  apply expression_equivalent_exists,expression_equivalent_conjunction;[apply expression_equivalent_refl|exact HE].
Qed.

Lemma raw_coverage_expression_equivalent M rho T A C U V theta theta' :
  expression_equivalent M rho theta theta' ->
  expression_equivalent M rho (E_raw_collection_coverage T A C U V theta)
    (E_raw_collection_coverage T A C U V theta').
Proof.
  intro HE;unfold E_raw_collection_coverage.
  apply expression_equivalent_implication;[apply expression_equivalent_refl|].
  apply expression_equivalent_implication.
  - apply expression_equivalent_exists,expression_equivalent_conjunction;[apply expression_equivalent_refl|exact HE].
  - apply expression_equivalent_exists,expression_equivalent_conjunction;[apply expression_equivalent_refl|].
    apply expression_equivalent_conjunction;[apply expression_equivalent_refl|exact HE].
Qed.

Lemma raw_profile_expression_equivalent M rho T A C U V theta theta' :
  expression_equivalent M rho theta theta' ->
  expression_equivalent M rho (E_raw_collection_profile T A C U V theta)
    (E_raw_collection_profile T A C U V theta').
Proof.
  intro HE;unfold E_raw_collection_profile.
  apply expression_equivalent_conjunction;[apply expression_equivalent_refl|].
  apply expression_equivalent_conjunction;apply expression_equivalent_all.
  - now apply raw_coverage_expression_equivalent.
  - now apply raw_support_expression_equivalent.
Qed.

Theorem raw_profile_matrix_equivalence M t a c u v theta theta' profile profile' :
  numerical_equivalent M theta theta' ->
  code_relation M (raw_clause_parameters M t a c u v theta)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  code_relation M (raw_clause_parameters M t a c u v theta')
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile' ->
  numerical_equivalent M profile profile'.
Proof.
  intros HE HP HP'. set (rho:=t .: a .: c .: u .: v .: theta .: theta' .: fun _=>zeroM M).
  assert (GP : code_relation M rho
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile) by exact HP.
  assert (GP' : code_relation M rho
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 6)) profile') by exact HP'.
  apply (proj1 (numerical_equivalent_expression M rho _ _ profile profile' GP GP')).
  apply raw_profile_expression_equivalent.
  exact (proj2 (numerical_equivalent_expression M rho (CEvar 5) (CEvar 6) theta theta' eq_refl eq_refl) HE).
Qed.

Print Assumptions raw_profile_expression_equivalent.
Print Assumptions raw_profile_matrix_equivalence.
