(** Expression-level rules for quantifier vacuity. These theorems allow
    arbitrary repeated binders in the matrix; no freshness is assumed. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros QuantifierMacros NumericalVacuitySteps NamedLeibnizSteps
  NamedAlpha NamedExistential BoundVariableVacuity.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem ns_bound_universal_vacuity M env X A :
  ns_proof M env (E_vac X (E_wal X A)).
Proof.
  intros result HR.
  destruct (code_relation_total M X env) as [x HX].
  destruct (code_relation_total M A env) as [a HA].
  destruct (code_relation_total M (E_wal X A) env) as [allf HAll].
  apply (numerical_bound_variable_vacuity M a x allf result).
  - exact (expression_universal_graph M env X A x a allf HX HA HAll).
  - exact (proj1 (expression_vacuity_graph M env X (E_wal X A) x allf result HX HAll) HR).
Qed.

Theorem ns_bound_existential_vacuity M env X A :
  ns_proof M env (E_vac X (E_wex X A)).
Proof.
  unfold E_wex.
  apply (ns_proof_macro M env (E_vac X (E_wal X (E_wn A)) :: nil)).
  - intros p [<-|[]]. apply ns_bound_universal_vacuity.
  - apply macro_vacuous_negation,PM_input. now left.
Qed.

Theorem numerical_bound_existential_vacuity M f x exf result :
  named_exists_graph M x f exf -> vacuity_graph M x exf result ->
  numerically_provable M result.
Proof.
  intros HE HR. set (env:=x .: f .: fun _=>zeroM M).
  assert (HC : code_relation M env (E_wex (CEvar 0) (CEvar 1)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 1)
      x f exf eq_refl eq_refl) HE). }
  apply (ns_bound_existential_vacuity M env (CEvar 0) (CEvar 1)).
  exact (proj2 (expression_vacuity_graph M env (CEvar 0)
    (E_wex (CEvar 0) (CEvar 1)) x exf result eq_refl HC) HR).
Qed.

Print Assumptions ns_bound_universal_vacuity.
Print Assumptions ns_bound_existential_vacuity.
Print Assumptions numerical_bound_existential_vacuity.
