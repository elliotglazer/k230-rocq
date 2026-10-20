(** Actual arithmetic construction of the ambient schema instances used by
    the WF interpretation. Codes and closure lengths may be nonstandard.
    These are inputs to the remaining source proof macros, not those proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetCodeDescent SourceBounded NumericalInstantiation SourceDomainInstances
  SourceRelativization SourceRelativizationBounds NumericalCoreAxioms
  NumericalZFCAxioms NumericalZFCClosure.
Unset Implicit Arguments.

Definition relative_replacement_matrix M domain rphi matrix :=
  exists domain1 guards,
    numerical_instantiation M domain (code_numeral M 1) domain1 /\
    sf_relation M SFAnd domain domain1 guards /\
    sf_relation M SFAnd guards rphi matrix.

Theorem relative_replacement_matrix_total M domain rphi :
  exists matrix,relative_replacement_matrix M domain rphi matrix.
Proof.
  destruct (numerical_instantiation_total M domain (code_numeral M 1)) as [d1 HD1].
  destruct (sf_relation_total M SFAnd domain d1) as [guards HG].
  destruct (sf_relation_total M SFAnd guards rphi) as [matrix HM].
  exists matrix,d1,guards. auto.
Qed.

Theorem relative_replacement_matrix_bound M domain rphi matrix n :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M rphi (succM M (succM M n)) ->
  relative_replacement_matrix M domain rphi matrix ->
  source_bounded M matrix (succM M (succM M n)).
Proof.
  intros HD HP [d1 [guards [HD1 [HG HM]]]].
  apply (proj2 (source_bounded_accept_binary M SFAnd guards rphi matrix
    (succM M (succM M n)) (or_introl eq_refl) HM)). split;[|exact HP].
  apply (proj2 (source_bounded_accept_binary M SFAnd domain d1 guards
    (succM M (succM M n)) (or_introl eq_refl) HG)). split.
  - exact (sr_domain_bound_succ M domain (succM M n) HD).
  - apply (source_domain_instance_bound M domain (code_numeral M 1) d1
      (succM M (succM M n)) HD).
    + change (coding_lt M (succM M (zeroM M)) (succM M (succM M n))).
      apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M n))),coding_zero_lt_succ.
    + exact HD1.
Qed.

Theorem source_relative_separation_input M domain phi rphi n :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M phi (succM M n) -> source_relativization M domain phi rphi ->
  exists ax,numerical_separation_instance M rphi n ax /\ numerical_zfc_core_source_axiom M ax.
Proof.
  intros HD HP HR.
  pose proof (source_relativization_preserves_bound M phi domain (succM M n) rphi HD HP HR) as HB.
  destruct (numerical_separation_closed_total M rphi n HB) as [ax [HA HC]].
  exists ax. split;[exact HA|right;left;exact HC].
Qed.

Theorem source_relative_replacement_input M domain phi rphi n :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M phi (succM M (succM M n)) ->
  source_relativization M domain phi rphi ->
  exists matrix ax,relative_replacement_matrix M domain rphi matrix /\
    numerical_replacement_instance M matrix n ax /\ numerical_zfc_core_source_axiom M ax.
Proof.
  intros HD HP HR.
  pose proof (source_relativization_preserves_bound M phi domain
    (succM M (succM M n)) rphi HD HP HR) as HB.
  destruct (relative_replacement_matrix_total M domain rphi) as [matrix HM].
  pose proof (relative_replacement_matrix_bound M domain rphi matrix n HD HB HM) as HMatrix.
  destruct (numerical_replacement_closed_total M matrix n HMatrix) as [ax [HA HC]].
  exists matrix,ax. split;[exact HM|]. split;[exact HA|right;right;exact HC].
Qed.

Print Assumptions relative_replacement_matrix_total.
Print Assumptions relative_replacement_matrix_bound.
Print Assumptions source_relative_separation_input.
Print Assumptions source_relative_replacement_input.
