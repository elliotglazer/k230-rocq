(** Unrestricted same-name specialization. Substitution stops at shadowing
    binders, and output-vacuity is proved by internal formula induction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  CodeDescent BetaExtension NumericalProofs NumericalEquality NumericalVacuitySteps NumericalVacuity
  FreshNames NamedSubstitution NamedBinderFresh NamedLeibnizSteps NamedLeibniz
  NamedSubstitutionVacuity NamedSpecialization NamedAlpha
  StoppingLeibniz BoundVariableVacuity BoundVariableVacuityRules
  ProofTemplates ProofMacros TemplateCD TemplatePropositional QuantifierMacros NamedExistential.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_stopping_self_specialization M f x allf result :
  universal_graph M x f allf ->
  implication_graph M allf f result -> numerically_provable M result.
Proof.
  intros HAll HResult.
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
  destruct (stopping_leibniz_internal M f x y eq v HE HY HV) as [HForward HBack].
  assert (PL : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 2) (CEvar 3)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 2) (CEvar 3) eq f v HEq eq_refl eq_refl) HForward). }
  assert (PR : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 3) (CEvar 2)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 3) (CEvar 2) eq v f HEq eq_refl eq_refl) HBack). }
  assert (VX : ns_proof M env (E_vac (CEvar 0) (CEvar 3))).
  { intros q HQ. apply (stopping_substitution_vacuity_internal M f x y v Hxy HV q).
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



Theorem ns_stopping_self_specialization M env X A :
  ns_proof M env (E_wim (E_wal X A) A).
Proof.
  intros result HR.
  destruct (code_relation_total M X env) as [x HX].
  destruct (code_relation_total M A env) as [a HA].
  destruct (code_relation_total M (E_wal X A) env) as [allf HAll].
  apply (numerical_stopping_self_specialization M a x allf result).
  - exact (expression_universal_graph M env X A x a allf HX HA HAll).
  - exact (expression_implication_graph M env (E_wal X A) A allf a result HAll HA HR).
Qed.

Lemma stopping_double_negation G A : template_proof G (E_wim A (E_wn (E_wn A))).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  eapply dmp;apply dhyp;cbn;tauto.
Qed.

Theorem ns_stopping_self_existential M env X A :
  ns_proof M env (E_wim A (E_wex X A)).
Proof.
  apply (ns_proof_macro M env (E_wim (E_wal X (E_wn A)) (E_wn A) :: nil)).
  - intros p [<-|[]]. apply ns_stopping_self_specialization.
  - unfold E_wex. eapply macro_syl.
    + apply PM_template,stopping_double_negation.
    + apply macro_contra,PM_input. now left.
Qed.

Theorem numerical_stopping_self_existential M f x exf result :
  named_exists_graph M x f exf -> implication_graph M f exf result ->
  numerically_provable M result.
Proof.
  intros HE HR. set (env:=x .: f .: fun _=>zeroM M).
  assert (HC : code_relation M env (E_wex (CEvar 0) (CEvar 1)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 1)
      x f exf eq_refl eq_refl) HE). }
  apply (ns_stopping_self_existential M env (CEvar 0) (CEvar 1)).
  exact (proj2 (expression_implication_iff M env (CEvar 1)
    (E_wex (CEvar 0) (CEvar 1)) f exf result eq_refl HC) HR).
Qed.

Print Assumptions numerical_stopping_self_specialization.
Print Assumptions ns_stopping_self_specialization.
Print Assumptions ns_stopping_self_existential.
Print Assumptions numerical_stopping_self_existential.
