(** Universal specialization and existential introduction with stopping
    substitution. Only the replacement name is excluded from binders. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates TemplatePropositional ProofMacros
  QuantifierMacros NumericalEquality NumericalVacuitySteps
  NamedSubstitution NamedBinderFresh NamedLeibnizSteps NamedSpecialization
  NamedAlpha NamedExistential StoppingLeibniz BoundVariableVacuity.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem ns_stopping_instantiation M env X Y A V x y f v :
  code_relation M env X x -> code_relation M env Y y ->
  code_relation M env A f -> code_relation M env V v ->
  x<>y -> named_binder_absent M f y -> named_substitution M f x y v ->
  ns_proof M env (E_wim (E_wal X A) V) /\
  ns_proof M env (E_wim V (E_wex X A)).
Proof.
  intros HX HY HA HV Hxy Habs Hsub.
  destruct (code_relation_total M (E_weq X Y) env) as [eq HEq].
  assert (HE : equality_graph M x y eq).
  { exact (proj1 (expression_equality_graph M env X Y x y eq HX HY) HEq). }
  destruct (stopping_leibniz_internal M f x y eq v HE Habs Hsub) as [HL HR].
  assert (PL : ns_proof M env (E_wim (E_weq X Y) (E_wim A V))).
  { exact (proj2 (ns_under_expression M env (E_weq X Y) A V eq f v HEq HA HV) HL). }
  assert (PR : ns_proof M env (E_wim (E_weq X Y) (E_wim V A))).
  { exact (proj2 (ns_under_expression M env (E_weq X Y) V A eq v f HEq HV HA) HR). }
  assert (VX : ns_proof M env (E_vac X V)).
  { intros q HQ. apply (stopping_substitution_vacuity_internal M f x y v Hxy Hsub q).
    exact (proj1 (expression_vacuity_graph M env X V x v q HX HV) HQ). }
  split.
  - exact (ns_proof_specialize M env X Y A V PL VX).
  - apply (ns_proof_macro M env
      (E_wim (E_weq X Y) (E_wim V A) :: E_vac X V :: nil)).
    + intros e [<-|[<-|[]]];assumption.
    + apply ns_macro_exists_intro.
Qed.

Theorem numerical_stopping_specialization M f x y v allf result :
  x<>y -> named_binder_absent M f y -> named_substitution M f x y v ->
  universal_graph M x f allf -> implication_graph M allf v result ->
  numerically_provable M result.
Proof.
  intros Hxy Habs Hsub HAll HResult.
  set (env:=code_parameters x y f v).
  pose proof (proj1 (ns_stopping_instantiation M env
    (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) x y f v
    eq_refl eq_refl eq_refl eq_refl Hxy Habs Hsub)) as HP.
  assert (HA : code_relation M env (E_wal (CEvar 0) (CEvar 2)) allf).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2)
      x f allf eq_refl eq_refl) HAll). }
  apply HP. exact (proj2 (expression_implication_iff M env
    (E_wal (CEvar 0) (CEvar 2)) (CEvar 3) allf v result HA eq_refl) HResult).
Qed.

Theorem numerical_stopping_exists_intro M f x y v exf result :
  x<>y -> named_binder_absent M f y -> named_substitution M f x y v ->
  named_exists_graph M x f exf -> implication_graph M v exf result ->
  numerically_provable M result.
Proof.
  intros Hxy Habs Hsub HEx HResult.
  set (env:=code_parameters x y f v).
  pose proof (proj2 (ns_stopping_instantiation M env
    (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) x y f v
    eq_refl eq_refl eq_refl eq_refl Hxy Habs Hsub)) as HP.
  assert (HA : code_relation M env (E_wex (CEvar 0) (CEvar 2)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 2)
      x f exf eq_refl eq_refl) HEx). }
  apply HP. exact (proj2 (expression_implication_iff M env
    (CEvar 3) (E_wex (CEvar 0) (CEvar 2)) v exf result eq_refl HA) HResult).
Qed.

Theorem numerical_stopping_specialization_total M f x y allf :
  x<>y -> named_binder_absent M f y -> universal_graph M x f allf ->
  exists v result,named_substitution M f x y v /\
    implication_graph M allf v result /\ numerically_provable M result.
Proof.
  intros Hxy Habs HAll.
  destruct (named_substitution_binder_absent_total M f x y Habs) as [v HV].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf v (zeroM M))) as [r HR].
  exists v,r. split;[exact HV|]. split;[exact HR|].
  exact (numerical_stopping_specialization M f x y v allf r Hxy Habs HV HAll HR).
Qed.

Theorem numerical_stopping_exists_intro_total M f x y :
  x<>y -> named_binder_absent M f y ->
  exists v exf result,named_substitution M f x y v /\
    named_exists_graph M x f exf /\ implication_graph M v exf result /\
    numerically_provable M result.
Proof.
  intros Hxy Habs.
  destruct (named_substitution_binder_absent_total M f x y Habs) as [v HV].
  destruct (named_exists_graph_total M x f) as [exf HEx].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 v exf (zeroM M))) as [r HR].
  exists v,exf,r. split;[exact HV|]. split;[exact HEx|]. split;[exact HR|].
  exact (numerical_stopping_exists_intro M f x y v exf r Hxy Habs HV HEx HR).
Qed.

Print Assumptions ns_stopping_instantiation.
Print Assumptions numerical_stopping_specialization.
Print Assumptions numerical_stopping_exists_intro.
Print Assumptions numerical_stopping_specialization_total.
Print Assumptions numerical_stopping_exists_intro_total.
