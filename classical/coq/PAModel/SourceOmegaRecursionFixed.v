(** An actual closed ZFR certificate for an omega recursion domain with a
    zero element and total/injective/nonzero/inductive successor relation.
    The varying-matrix set-recursion kernel is separate work. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
  SourceOmegaRecursionOld OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
Unset Implicit Arguments.

Definition source_omega_recursion_body :sf_form:=isolated_formula old_omega_recursion_body.
Definition source_omega_recursion_inner :sf_form:=isolated_formula old_omega_recursion_inner.
Definition source_omega_recursion_form :sf_form:=isolated_formula old_omega_recursion_structure.
Definition source_omega_recursion_body_code M:=code_numeral M(sf_encode source_omega_recursion_body).
Definition source_omega_recursion_inner_code M:=code_numeral M(sf_encode source_omega_recursion_inner).
Definition source_omega_recursion_code M:=code_numeral M(sf_encode source_omega_recursion_form).

Theorem source_omega_recursion_inner_graph M:
  sf_relation M SFEx(source_omega_recursion_body_code M)(zeroM M)(source_omega_recursion_inner_code M).
Proof. exact(sf_make_numeral M SFEx(sf_encode source_omega_recursion_body)0). Qed.
Theorem source_omega_recursion_outer_graph M:
  sf_relation M SFEx(source_omega_recursion_inner_code M)(zeroM M)(source_omega_recursion_code M).
Proof. exact(sf_make_numeral M SFEx(sf_encode source_omega_recursion_inner)0). Qed.
Theorem source_zfr_omega_recursion_structure M:source_zfr_provable M(source_omega_recursion_code M).
Proof.
  exact(finite_old_zfr_proof_lift M old_omega_recursion_background old_omega_recursion_structure
    old_omega_recursion_background_valid old_omega_recursion_structure_proof).
Qed.

Print Assumptions source_omega_recursion_inner_graph.
Print Assumptions source_omega_recursion_outer_graph.
Print Assumptions source_zfr_omega_recursion_structure.
