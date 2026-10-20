(** Specialization to the same variable name. The matrix may use the name
    freely, but no inner binder may use it. An auxiliary fresh name and the
    two directions of Leibniz avoid assuming a substitution round trip. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  CodeDescent BetaExtension NumericalProofs NumericalEquality NumericalVacuitySteps NumericalVacuity
  FreshNames NamedSubstitution NamedBinderFresh NamedLeibnizSteps NamedLeibniz
  NamedSubstitutionVacuity NamedSpecialization NamedAlpha.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem numerical_named_self_specialization M f x allf result :
  named_binder_absent M f x -> universal_graph M x f allf ->
  implication_graph M allf f result -> numerically_provable M result.
Proof.
  intros HX HAll HResult.
  set (y:=succM M (addM M x f)).
  assert (HXY : coding_lt M x y) by (unfold y;apply coding_le_add).
  assert (HFY : coding_lt M f y).
  { unfold y. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (Hxy : x<>y).
  { exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) x y HXY). }
  pose proof (formula_above_is_fresh M f y HFY) as HYFresh.
  pose proof (named_formula_fresh_binder_absent M f y HYFresh) as HY.
  destruct (named_substitution_binder_absent_total M f x y HY) as [v HV].
  set (env:=code_parameters x y f v).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1)) env) as [eq HEq].
  assert (HE : equality_graph M x y eq).
  { exact (proj1 (expression_equality_graph M env (CEvar 0) (CEvar 1) x y eq eq_refl eq_refl) HEq). }
  destruct (named_leibniz_internal M f x y eq v HE HX HY HV) as [HForward HBack].
  assert (PL : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 2) (CEvar 3)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 2) (CEvar 3) eq f v HEq eq_refl eq_refl) HForward). }
  assert (PR : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 3) (CEvar 2)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 3) (CEvar 2) eq v f HEq eq_refl eq_refl) HBack). }
  assert (VX : ns_proof M env (E_vac (CEvar 0) (CEvar 3))).
  { intros q HQ. apply (numerical_named_substitution_vacuity M f x y v q Hxy HX HV).
    exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 3) x v q eq_refl eq_refl) HQ). }
  assert (VY : ns_proof M env (E_vac (CEvar 1) (CEvar 2))).
  { intros q HQ. apply (numerical_vacuity M y f q HYFresh).
    exact (proj1 (expression_vacuity_graph M env (CEvar 1) (CEvar 2) y f q eq_refl eq_refl) HQ). }
  pose proof (proj1 (ns_proof_alpha M env (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) PL PR VX VY)) as PA.
  assert (PS : ns_proof M env (E_wim (E_wal (CEvar 1) (CEvar 3)) (CEvar 2))).
  { apply (ns_proof_specialize M env (CEvar 1) (CEvar 0) (CEvar 3) (CEvar 2));[|exact VY].
    eapply ns_proof_syl;[apply ns_proof_symmetry|exact PR]. }
  pose proof (ns_proof_syl M env (E_wal (CEvar 0) (CEvar 2))
    (E_wal (CEvar 1) (CEvar 3)) (CEvar 2) PA PS) as HP.
  assert (HA : code_relation M env (E_wal (CEvar 0) (CEvar 2)) allf).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2)
      x f allf eq_refl eq_refl) HAll). }
  apply HP.
  exact (proj2 (expression_implication_iff M env
    (E_wal (CEvar 0) (CEvar 2)) (CEvar 2) allf f result HA eq_refl) HResult).
Qed.

Print Assumptions numerical_named_self_specialization.
