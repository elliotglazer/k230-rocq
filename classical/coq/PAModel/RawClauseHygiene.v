(** The raw clauses introduce only their displayed witness binder; free
    variable occurrences do not invalidate binder-absence for alpha conversion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NamedBinderFresh
  TemplateBinderFresh RawCollectionProfile RawClauseAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem raw_support_clause_binder_absent M t a c u v theta body name :
  u<>name -> named_binder_absent M theta name ->
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_support_clause body ->
  named_binder_absent M body name.
Proof.
  intros HU HT HB;set (rho:=raw_clause_parameters M t a c u v theta).
  assert (HTheta : expression_binder_absent M rho name (CEvar 5)).
  { intros z HZ;change (z=theta) in HZ;now subst z. }
  assert (H : expression_binder_absent M rho name E_raw_support_clause).
  { unfold E_raw_support_clause,E_raw_collection_support.
    apply expression_binder_absent_implication.
    - apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now left.
    - apply expression_binder_absent_existential.
      + intros z HZ;change (z=u) in HZ;now subst z.
      + apply expression_binder_absent_conjunction;[|exact HTheta].
        apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now left. }
  exact (H body HB).
Qed.

Theorem raw_coverage_clause_binder_absent M t a c u v theta body name :
  v<>name -> named_binder_absent M theta name ->
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_coverage_clause body ->
  named_binder_absent M body name.
Proof.
  intros HV HT HB;set (rho:=raw_clause_parameters M t a c u v theta).
  assert (HTheta : expression_binder_absent M rho name (CEvar 5)).
  { intros z HZ;change (z=theta) in HZ;now subst z. }
  assert (H : expression_binder_absent M rho name E_raw_coverage_clause).
  { unfold E_raw_coverage_clause,E_raw_collection_coverage.
    apply expression_binder_absent_implication.
    - apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now left.
    - apply expression_binder_absent_implication;apply expression_binder_absent_existential.
      + intros z HZ;change (z=v) in HZ;now subst z.
      + apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|exact HTheta].
      + intros z HZ;change (z=v) in HZ;now subst z.
      + apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|].
        apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|exact HTheta]. }
  exact (H body HB).
Qed.

Print Assumptions raw_support_clause_binder_absent.
Print Assumptions raw_coverage_clause_binder_absent.
