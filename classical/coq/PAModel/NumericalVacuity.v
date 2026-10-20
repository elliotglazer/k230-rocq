(** A genuine internal K proof of p -> forall x p when x is absent from
    the named numerical syntax of p. Induction is PA-definable and applies
    to nonstandard formula codes as well as standard ones. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs ProofTemplates TemplatePropositional KInternalLogic
  CodeDescent FreshNames FreshPropagation NumericalVacuitySteps ProofMacros QuantifierMacros.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition E_atom (equality : bool) a b := if equality then E_weq a b else E_wel a b.

Lemma atom_expression_graph M equality a b f :
  code_relation M (code_parameters a b (zeroM M) (zeroM M))
    (E_atom equality (CEvar 0) (CEvar 1)) f <->
  tagged_pair_graph M (if equality then 3 else 1) a b f.
Proof.
  destruct equality; unfold E_atom,E_weq,E_wel,E_wim;
    cbn [code_relation code_parameters]; split.
  all: try (intros [q [r [[four [p [Hfour [[u [v [Hu [Hv Hp]]]] Hq]]]] [Hr Hf]]]];
    subst four u v r q; exists p; auto).
  all: intros [p [Hp Hf]]; eexists (mulM M (code_numeral M 4) p), _; split.
  all: try (exists (code_numeral M 4),p;
    split; [reflexivity|]; split; [exists a,b;auto|reflexivity]).
  all: split; [reflexivity|exact Hf].
Qed.

Lemma template_atom_vacuity G equality a b x :
  In (x,a) G -> In (x,b) G -> template_proof G (E_vac x (E_atom equality a b)).
Proof.
  intros Ha Hb. apply template_discharge.
  destruct equality; unfold E_atom,E_vac.
  - eapply template_der_andl. apply dthm. exact (template_B6a G a b x Ha Hb).
  - eapply template_der_andr. apply dthm. exact (template_B6a G a b x Ha Hb).
Qed.

Lemma numerical_atom_vacuity M (equality : bool) a b f x v :
  tagged_pair_graph M (if equality then 3 else 1) a b f ->
  x<>a -> x<>b -> vacuity_graph M x f v -> numerically_provable M v.
Proof.
  intros Hf Hxa Hxb Hv.
  set (env := code_parameters a b x (zeroM M)).
  assert (Hatom : code_relation M env (E_atom equality (CEvar 0) (CEvar 1)) f).
  { apply (proj2 (atom_expression_graph M equality a b f)) in Hf.
    destruct equality; exact Hf. }
  apply (template_sound M env K_parameter_guards
    (E_vac (CEvar 2) (E_atom equality (CEvar 0) (CEvar 1)))
    (K_parameter_guards_correct M a b x Hxa Hxb)).
  - apply template_atom_vacuity; cbn; tauto.
  - exact (proj2 (expression_vacuity_graph M env (CEvar 2)
      (E_atom equality (CEvar 0) (CEvar 1)) x f v eq_refl Hatom) Hv).
Qed.

Definition internal_vacuity_at M x f := formula_fresh M f x ->
  exists v, vacuity_graph M x f v /\ numerically_provable M v.

Definition internal_vacuity_formula : form :=
  formula_fresh_formula $0 $1 →
    ∃ (vacuity_formula $2 $1 $0 ∧ numerically_provable_formula $0).

Local Opaque holds formula_fresh_formula vacuity_formula numerically_provable_formula.
Lemma internal_vacuity_definable M x : Definable1 M (internal_vacuity_at M x).
Proof.
  exists internal_vacuity_formula,(x .: fun _ => zeroM M). intro f.
  unfold internal_vacuity_formula,internal_vacuity_at.
  rewrite holds_imp,formula_fresh_formula_correct.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite vacuity_formula_correct. setoid_rewrite numerically_provable_formula_correct.
  reflexivity.
Qed.

Theorem internal_vacuity_exists M x f : internal_vacuity_at M x f.
Proof.
  revert f. apply (named_formula_code_induction M (internal_vacuity_at M x)).
  - apply internal_vacuity_definable.
  - intro Hfresh. destruct (vacuity_graph_total M x (zeroM M)) as [v Hv].
    exists v. split; [exact Hv|].
    apply (numerical_vacuity_truth M (x .: fun _ => zeroM M) (CEvar 0) v).
    exact (proj2 (expression_vacuity_graph M _ (CEvar 0) (CEconst 0)
      x (zeroM M) v eq_refl eq_refl) Hv).
  - intros a b f Hf Hfresh.
    destruct (formula_fresh_membership M a b f x Hf Hfresh) as [Ha Hb].
    destruct (vacuity_graph_total M x f) as [v Hv]. exists v. split; [exact Hv|].
    apply (numerical_atom_vacuity M false a b f x v Hf); try congruence; exact Hv.
  - intros a b f Hf Hfresh.
    destruct (formula_fresh_equality M a b f x Hf Hfresh) as [Ha Hb].
    destruct (vacuity_graph_total M x f) as [v Hv]. exists v. split; [exact Hv|].
    apply (numerical_atom_vacuity M true a b f x v Hf); try congruence; exact Hv.
  - intros a b f Hnz Hf IHa IHb Hfresh.
    destruct (formula_fresh_implication M a b f x Hnz Hf Hfresh) as [Ha Hb].
    destruct (IHa Ha) as [va [Hva Hpa]]. destruct (IHb Hb) as [vb [Hvb Hpb]].
    destruct (vacuity_graph_total M x f) as [v Hv]. exists v. split; [exact Hv|].
    set (env := code_parameters x a b (zeroM M)).
    assert (Hformula : code_relation M env (E_wim (CEvar 1) (CEvar 2)) f).
    { exact (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2) a b f eq_refl eq_refl) Hf). }
    apply (numerical_vacuity_implication M env (CEvar 0) (CEvar 1) (CEvar 2) va vb v).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 1) x a va eq_refl eq_refl) Hva).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 2) x b vb eq_refl eq_refl) Hvb).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) x f v eq_refl Hformula) Hv).
    + exact Hpa.
    + exact Hpb.
  - intros a b f Hf IH Hfresh.
    destruct (formula_fresh_universal M a b f x Hf Hfresh) as [_ Hb].
    destruct (IH Hb) as [vb [Hvb Hpb]].
    destruct (vacuity_graph_total M x f) as [v Hv]. exists v. split; [exact Hv|].
    set (env := code_parameters x a b (zeroM M)).
    assert (Hformula : code_relation M env (E_wal (CEvar 1) (CEvar 2)) f).
    { exact (proj2 (expression_universal_iff M env (CEvar 1) (CEvar 2) a b f eq_refl eq_refl) Hf). }
    apply (numerical_vacuity_universal M env (CEvar 1) (CEvar 0) (CEvar 2) vb v).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 2) x b vb eq_refl eq_refl) Hvb).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (E_wal (CEvar 1) (CEvar 2)) x f v eq_refl Hformula) Hv).
    + exact Hpb.
Qed.

Theorem numerical_vacuity M x f v : formula_fresh M f x ->
  vacuity_graph M x f v -> numerically_provable M v.
Proof.
  intros Hfresh Hv. destruct (internal_vacuity_exists M x f Hfresh) as [w [Hw Hpw]].
  assert (v=w) by exact (vacuity_graph_functional M x f v w Hv Hw). now subst v.
Qed.

(** Generalizing the conclusion of a derivation under one fixed hypothesis.
    The hypothesis itself is not assumed globally provable. *)
Theorem numerical_generalization_under_hypothesis M x h f premise quantified result :
  formula_fresh M h x -> implication_graph M h f premise ->
  universal_graph M x f quantified -> implication_graph M h quantified result ->
  numerically_provable M premise -> numerically_provable M result.
Proof.
  intros Hfresh Hprem Hquant Hresult Hproof.
  set (env := code_parameters x h f (zeroM M)).
  destruct (vacuity_graph_total M x h) as [v Hv].
  pose proof (numerical_vacuity M x h v Hfresh Hv) as Hpv.
  assert (Hp : code_relation M env (E_wim (CEvar 1) (CEvar 2)) premise).
  { exact (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2)
      h f premise eq_refl eq_refl) Hprem). }
  assert (Hvac : code_relation M env (E_vac (CEvar 0) (CEvar 1)) v).
  { exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 1)
      x h v eq_refl eq_refl) Hv). }
  assert (Hq : code_relation M env (E_wal (CEvar 0) (CEvar 2)) quantified).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2)
      x f quantified eq_refl eq_refl) Hquant). }
  assert (Hr : code_relation M env (E_wim (CEvar 1) (E_wal (CEvar 0) (CEvar 2))) result).
  { exact (proj2 (expression_implication_iff M env (CEvar 1) _
      h quantified result eq_refl Hq) Hresult). }
  apply (unguarded_macro_sound M env
    (E_wim (CEvar 1) (CEvar 2) :: E_vac (CEvar 0) (CEvar 1) :: nil)
    (E_wim (CEvar 1) (E_wal (CEvar 0) (CEvar 2)))
    (macro_two_inputs M env _ _ premise v Hp Hvac Hproof Hpv)); [|exact Hr].
  eapply (macro_syl _ _ (CEvar 1) (E_wal (CEvar 0) (CEvar 1))).
  - apply PM_input. cbn. auto.
  - apply macro_all_monotone,PM_input. now left.
Qed.

Definition numerical_vacuity_sentence : form := ∀∀ internal_vacuity_formula.

Theorem numerical_vacuity_sentence_true M rho : holds M rho numerical_vacuity_sentence.
Proof.
  unfold numerical_vacuity_sentence. rewrite holds_all. intro x.
  rewrite holds_all. intro f. unfold internal_vacuity_formula.
  rewrite holds_imp,formula_fresh_formula_correct.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite vacuity_formula_correct. setoid_rewrite numerically_provable_formula_correct.
  exact (internal_vacuity_exists M x f).
Qed.

Print Assumptions internal_vacuity_definable.
Print Assumptions internal_vacuity_exists.
Print Assumptions numerical_vacuity.
Print Assumptions numerical_generalization_under_hypothesis.
Print Assumptions numerical_vacuity_sentence_true.
