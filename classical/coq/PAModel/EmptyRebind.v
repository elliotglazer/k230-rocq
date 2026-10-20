(** Empty-marker profiles can be rebased to a fresh numerical binder. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps RawMarkerExclusions RawMarkerQuantifiers NumericalKP0Eligibility.
Unset Implicit Arguments.

Theorem numerical_empty_rebind M rho T Z W tv zv wv :
  code_relation M rho T tv -> code_relation M rho Z zv -> code_relation M rho W wv ->
  zv<>zeroM M -> wv<>zeroM M -> zv<>wv -> tv<>zv -> tv<>wv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_marker_empty T W)).
Proof.
  intros HT HZ HW HZ0 HW0 HZW HTZ HTW. apply marker_generalize_one.
  - apply (kp0_expression_fresh_vacuity M rho W (E_marker_empty T Z) wv HW).
    exact (marker_empty_fresh M rho T Z tv zv wv HT HZ HW0 HTW HZW).
  - exact (marker_empty_specialization M rho T Z W tv zv wv HT HZ HW HZ0 HZW HTZ).
Qed.

Print Assumptions numerical_empty_rebind.
