(** Full freshness of the finite raw Collection formulas. This is used
    when the original profile remains in the local context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions FreshNames TemplateFormulaFresh
  RawCollectionProfile RawClauseAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma raw_support_expression_fresh M rho name T A C U V theta :
  name<>zeroM M -> expression_name_avoids M rho name T -> expression_name_avoids M rho name A ->
  expression_name_avoids M rho name C -> expression_name_avoids M rho name U ->
  expression_name_avoids M rho name V -> expression_fresh M rho name theta ->
  expression_fresh M rho name (E_raw_collection_support T A C U V theta).
Proof.
  intros H0 HT HA HC HU HV HTheta;unfold E_raw_collection_support.
  apply expression_fresh_implication.
  - apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_atom;[now left|exact HT|exact HV].
    + apply expression_fresh_atom;[now left|exact HV|exact HC].
  - apply expression_fresh_existential;[exact H0|exact HU|].
    apply expression_fresh_conjunction;[exact H0| |exact HTheta].
    apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_atom;[now left|exact HT|exact HU].
    + apply expression_fresh_atom;[now left|exact HU|exact HA].
Qed.

Lemma raw_coverage_expression_fresh M rho name T A C U V theta :
  name<>zeroM M -> expression_name_avoids M rho name T -> expression_name_avoids M rho name A ->
  expression_name_avoids M rho name C -> expression_name_avoids M rho name U ->
  expression_name_avoids M rho name V -> expression_fresh M rho name theta ->
  expression_fresh M rho name (E_raw_collection_coverage T A C U V theta).
Proof.
  intros H0 HT HA HC HU HV HTheta;unfold E_raw_collection_coverage.
  apply expression_fresh_implication.
  - apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_atom;[now left|exact HT|exact HU].
    + apply expression_fresh_atom;[now left|exact HU|exact HA].
  - apply expression_fresh_implication.
    + apply expression_fresh_existential;[exact H0|exact HV|].
      apply expression_fresh_conjunction;[exact H0| |exact HTheta].
      apply expression_fresh_atom;[now left|exact HT|exact HV].
    + apply expression_fresh_existential;[exact H0|exact HV|].
      apply expression_fresh_conjunction;[exact H0| |].
      * apply expression_fresh_atom;[now left|exact HT|exact HV].
      * apply expression_fresh_conjunction;[exact H0| |exact HTheta].
        apply expression_fresh_atom;[now left|exact HV|exact HC].
Qed.

Lemma raw_profile_expression_fresh M rho name T A C U V theta :
  name<>zeroM M -> expression_name_avoids M rho name T -> expression_name_avoids M rho name A ->
  expression_name_avoids M rho name C -> expression_name_avoids M rho name U ->
  expression_name_avoids M rho name V -> expression_fresh M rho name theta ->
  expression_fresh M rho name (E_raw_collection_profile T A C U V theta).
Proof.
  intros H0 HT HA HC HU HV HTheta;unfold E_raw_collection_profile.
  apply expression_fresh_conjunction;[exact H0| |].
  - apply expression_fresh_atom;[now left|exact HT|exact HC].
  - apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_universal;[exact HU|]. now apply raw_coverage_expression_fresh.
    + apply expression_fresh_universal;[exact HV|]. now apply raw_support_expression_fresh.
Qed.

Theorem raw_profile_formula_fresh M t a c u v theta profile name :
  name<>zeroM M -> t<>name -> a<>name -> c<>name -> u<>name -> v<>name ->
  formula_fresh M theta name ->
  code_relation M (raw_clause_parameters M t a c u v theta)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  formula_fresh M profile name.
Proof.
  intros H0 HT HA HC HU HV HTheta HG;set (rho:=raw_clause_parameters M t a c u v theta).
  apply (raw_profile_expression_fresh M rho name (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5));try assumption.
  - intros z HZ;change (z=t) in HZ;now subst z.
  - intros z HZ;change (z=a) in HZ;now subst z.
  - intros z HZ;change (z=c) in HZ;now subst z.
  - intros z HZ;change (z=u) in HZ;now subst z.
  - intros z HZ;change (z=v) in HZ;now subst z.
  - intros z HZ;change (z=theta) in HZ;now subst z.
Qed.

Print Assumptions raw_support_expression_fresh.
Print Assumptions raw_coverage_expression_fresh.
Print Assumptions raw_profile_formula_fresh.
