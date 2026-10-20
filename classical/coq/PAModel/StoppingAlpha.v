(** Alphabetic variance for stopping substitution. Inner occurrences of the
    old binder are allowed. The replacement name remains absent from binder
    positions, and its vacuity in the original body is an explicit input.
    The freshness corollaries discharge both requirements syntactically. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs NumericalEquivalence ProofTemplates TemplatePropositional
  ProofMacros QuantifierMacros NumericalEquality NumericalVacuitySteps
  NumericalVacuity FreshNames NamedSubstitution NamedBinderFresh
  NamedLeibnizSteps NamedAlpha NamedExistential StoppingLeibniz
  BoundVariableVacuity.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma ns_conditional_contraposition M env H A B :
  ns_proof M env (E_wim H (E_wim A B)) ->
  ns_proof M env (E_wim H (E_wim (E_wn B) (E_wn A))).
Proof.
  intro HP. apply (ns_proof_macro M env (E_wim H (E_wim A B) :: nil)).
  - intros e [<-|[]]. exact HP.
  - eapply macro_syl;[apply PM_input;now left|].
    apply PM_template,template_contraposition.
Qed.

Lemma ns_proof_exists_alpha M env X Y A V :
  ns_proof M env (E_wim (E_weq X Y) (E_wim A V)) ->
  ns_proof M env (E_wim (E_weq X Y) (E_wim V A)) ->
  ns_proof M env (E_vac X V) -> ns_proof M env (E_vac Y A) ->
  ns_proof M env (E_wim (E_wex X A) (E_wex Y V)) /\
  ns_proof M env (E_wim (E_wex Y V) (E_wex X A)).
Proof.
  intros HL HR VX VY.
  assert (VXN : ns_proof M env (E_vac X (E_wn V))).
  { apply (ns_proof_macro M env (E_vac X V :: nil)).
    - intros e [<-|[]]. exact VX.
    - apply macro_vacuous_negation,PM_input;now left. }
  assert (VYN : ns_proof M env (E_vac Y (E_wn A))).
  { apply (ns_proof_macro M env (E_vac Y A :: nil)).
    - intros e [<-|[]]. exact VY.
    - apply macro_vacuous_negation,PM_input;now left. }
  destruct (ns_proof_alpha M env X Y (E_wn A) (E_wn V)
    (ns_conditional_contraposition M env (E_weq X Y) V A HR)
    (ns_conditional_contraposition M env (E_weq X Y) A V HL) VXN VYN) as [PF PB].
  unfold E_wex. split.
  - apply (ns_proof_macro M env (E_wim (E_wal Y (E_wn V)) (E_wal X (E_wn A)) :: nil)).
    + intros e [<-|[]]. exact PB.
    + apply macro_contra,PM_input;now left.
  - apply (ns_proof_macro M env (E_wim (E_wal X (E_wn A)) (E_wal Y (E_wn V)) :: nil)).
    + intros e [<-|[]]. exact PF.
    + apply macro_contra,PM_input;now left.
Qed.

(** The replacement's binder absence is all that Leibniz transport needs.
    A semantic vacuity proof can be used even when full syntactic freshness
    is inconvenient, for example for a formula with harmless bound names. *)
Theorem ns_stopping_alpha_inputs M env X Y A V x y f v :
  code_relation M env X x -> code_relation M env Y y ->
  code_relation M env A f -> code_relation M env V v ->
  x<>y -> named_binder_absent M f y -> named_substitution M f x y v ->
  ns_proof M env (E_vac Y A) ->
  (ns_proof M env (E_wim (E_wal X A) (E_wal Y V)) /\
   ns_proof M env (E_wim (E_wal Y V) (E_wal X A))) /\
  (ns_proof M env (E_wim (E_wex X A) (E_wex Y V)) /\
   ns_proof M env (E_wim (E_wex Y V) (E_wex X A))).
Proof.
  intros HX HY HA HV Hxy Habs Hsub VY.
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
  - exact (ns_proof_alpha M env X Y A V PL PR VX VY).
  - exact (ns_proof_exists_alpha M env X Y A V PL PR VX VY).
Qed.

Theorem ns_stopping_alpha M env X Y A V x y f v :
  code_relation M env X x -> code_relation M env Y y ->
  code_relation M env A f -> code_relation M env V v ->
  x<>y -> formula_fresh M f y -> named_substitution M f x y v ->
  (ns_proof M env (E_wim (E_wal X A) (E_wal Y V)) /\
   ns_proof M env (E_wim (E_wal Y V) (E_wal X A))) /\
  (ns_proof M env (E_wim (E_wex X A) (E_wex Y V)) /\
   ns_proof M env (E_wim (E_wex Y V) (E_wex X A))).
Proof.
  intros HX HY HA HV Hxy Hfresh Hsub.
  apply (ns_stopping_alpha_inputs M env X Y A V x y f v HX HY HA HV Hxy
    (named_formula_fresh_binder_absent M f y Hfresh) Hsub).
  intros q HQ. apply (numerical_vacuity M y f q Hfresh).
  exact (proj1 (expression_vacuity_graph M env Y A y f q HY HA) HQ).
Qed.

Theorem numerical_stopping_alpha M f x y v allf allv forward backward :
  x<>y -> formula_fresh M f y -> named_substitution M f x y v ->
  universal_graph M x f allf -> universal_graph M y v allv ->
  implication_graph M allf allv forward -> implication_graph M allv allf backward ->
  numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hxy Hfresh Hv HAllF HAllV HForward HBackward.
  set (env:=code_parameters x y f v).
  destruct (proj1 (ns_stopping_alpha M env (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
    x y f v eq_refl eq_refl eq_refl eq_refl Hxy Hfresh Hv)) as [PF PB].
  assert (EF : code_relation M env (E_wal (CEvar 0) (CEvar 2)) allf).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2)
      x f allf eq_refl eq_refl) HAllF). }
  assert (EV : code_relation M env (E_wal (CEvar 1) (CEvar 3)) allv).
  { exact (proj2 (expression_universal_iff M env (CEvar 1) (CEvar 3)
      y v allv eq_refl eq_refl) HAllV). }
  split.
  - apply PF. exact (proj2 (expression_implication_iff M env
      (E_wal (CEvar 0) (CEvar 2)) (E_wal (CEvar 1) (CEvar 3))
      allf allv forward EF EV) HForward).
  - apply PB. exact (proj2 (expression_implication_iff M env
      (E_wal (CEvar 1) (CEvar 3)) (E_wal (CEvar 0) (CEvar 2))
      allv allf backward EV EF) HBackward).
Qed.

Theorem numerical_stopping_exists_alpha M f x y v exf exv forward backward :
  x<>y -> formula_fresh M f y -> named_substitution M f x y v ->
  named_exists_graph M x f exf -> named_exists_graph M y v exv ->
  implication_graph M exf exv forward -> implication_graph M exv exf backward ->
  numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hxy Hfresh Hv HExF HExV HForward HBackward.
  set (env:=code_parameters x y f v).
  destruct (proj2 (ns_stopping_alpha M env (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
    x y f v eq_refl eq_refl eq_refl eq_refl Hxy Hfresh Hv)) as [PF PB].
  assert (EF : code_relation M env (E_wex (CEvar 0) (CEvar 2)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 2)
      x f exf eq_refl eq_refl) HExF). }
  assert (EV : code_relation M env (E_wex (CEvar 1) (CEvar 3)) exv).
  { exact (proj2 (named_exists_expression M env (CEvar 1) (CEvar 3)
      y v exv eq_refl eq_refl) HExV). }
  split.
  - apply PF. exact (proj2 (expression_implication_iff M env
      (E_wex (CEvar 0) (CEvar 2)) (E_wex (CEvar 1) (CEvar 3))
      exf exv forward EF EV) HForward).
  - apply PB. exact (proj2 (expression_implication_iff M env
      (E_wex (CEvar 1) (CEvar 3)) (E_wex (CEvar 0) (CEvar 2))
      exv exf backward EV EF) HBackward).
Qed.

Theorem numerical_stopping_alpha_equivalent M f x y v allf allv :
  x<>y -> formula_fresh M f y -> named_substitution M f x y v ->
  universal_graph M x f allf -> universal_graph M y v allv ->
  numerical_equivalent M allf allv.
Proof.
  intros Hxy HF HV HAF HAV. split;intros p HP.
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (arguments2 allv allf (zeroM M))) as [q HQ].
    exact (proj1 (numerical_stopping_alpha M f x y v allf allv p q Hxy HF HV HAF HAV HP HQ)).
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (arguments2 allf allv (zeroM M))) as [q HQ].
    exact (proj2 (numerical_stopping_alpha M f x y v allf allv q p Hxy HF HV HAF HAV HQ HP)).
Qed.

Theorem numerical_stopping_exists_alpha_equivalent M f x y v exf exv :
  x<>y -> formula_fresh M f y -> named_substitution M f x y v ->
  named_exists_graph M x f exf -> named_exists_graph M y v exv ->
  numerical_equivalent M exf exv.
Proof.
  intros Hxy HF HV HEF HEV. split;intros p HP.
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (arguments2 exv exf (zeroM M))) as [q HQ].
    exact (proj1 (numerical_stopping_exists_alpha M f x y v exf exv p q Hxy HF HV HEF HEV HP HQ)).
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (arguments2 exf exv (zeroM M))) as [q HQ].
    exact (proj2 (numerical_stopping_exists_alpha M f x y v exf exv q p Hxy HF HV HEF HEV HQ HP)).
Qed.

Theorem numerical_stopping_alpha_total M f x y allf :
  x<>y -> formula_fresh M f y -> universal_graph M x f allf ->
  exists v allv,named_substitution M f x y v /\ universal_graph M y v allv /\
    numerical_equivalent M allf allv.
Proof.
  intros Hxy HF HAll.
  destruct (named_substitution_binder_absent_total M f x y
    (named_formula_fresh_binder_absent M f y HF)) as [v HV].
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 1))
    (arguments2 y v (zeroM M))) as [allv HAllV].
  exists v,allv. split;[exact HV|]. split;[exact HAllV|].
  exact (numerical_stopping_alpha_equivalent M f x y v allf allv Hxy HF HV HAll HAllV).
Qed.

Theorem numerical_stopping_exists_alpha_total M f x y exf :
  x<>y -> formula_fresh M f y -> named_exists_graph M x f exf ->
  exists v exv,named_substitution M f x y v /\ named_exists_graph M y v exv /\
    numerical_equivalent M exf exv.
Proof.
  intros Hxy HF HEx.
  destruct (named_substitution_binder_absent_total M f x y
    (named_formula_fresh_binder_absent M f y HF)) as [v HV].
  destruct (named_exists_graph_total M y v) as [exv HExV].
  exists v,exv. split;[exact HV|]. split;[exact HExV|].
  exact (numerical_stopping_exists_alpha_equivalent M f x y v exf exv Hxy HF HV HEx HExV).
Qed.

Print Assumptions ns_stopping_alpha_inputs.
Print Assumptions ns_stopping_alpha.
Print Assumptions numerical_stopping_alpha.
Print Assumptions numerical_stopping_exists_alpha.
Print Assumptions numerical_stopping_alpha_total.
Print Assumptions numerical_stopping_exists_alpha_total.
