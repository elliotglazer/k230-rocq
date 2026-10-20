(** Concrete internal proof operations used by vacuous generalization. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs ProofClosure
  ProofTemplates TemplateCD TemplatePropositional ProofMacros QuantifierMacros.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition E_vac x p := E_wim p (E_wal x p).
Definition vacuity_graph M x p v :=
  code_relation M (x .: p .: fun _ => zeroM M) (E_vac (CEvar 0) (CEvar 1)) v.
Definition vacuity_formula (x p v : term) : form :=
  code_formula (E_vac (CEvar 0) (CEvar 1)) (x .: p .: fun _ => zero) v.

Lemma expression_implication_iff M env p q a b v :
  code_relation M env p a -> code_relation M env q b ->
  (code_relation M env (E_wim p q) v <-> implication_graph M a b v).
Proof.
  intros Hp Hq. unfold implication_graph.
  change (code_relation M env (code_subst (arguments2 p q (CEconst 0))
    (E_wim (CEvar 0) (CEvar 1))) v <->
    code_relation M (arguments2 a b (zeroM M)) (E_wim (CEvar 0) (CEvar 1)) v).
  apply code_subst_graph. intros [|[|i]]; [exact Hp|exact Hq|reflexivity].
Qed.

Lemma expression_universal_iff M env p q a b v :
  code_relation M env p a -> code_relation M env q b ->
  (code_relation M env (E_wal p q) v <-> universal_graph M a b v).
Proof.
  intros Hp Hq. unfold universal_graph.
  change (code_relation M env (code_subst (arguments2 p q (CEconst 0))
    (E_wal (CEvar 0) (CEvar 1))) v <->
    code_relation M (arguments2 a b (zeroM M)) (E_wal (CEvar 0) (CEvar 1)) v).
  apply code_subst_graph. intros [|[|i]]; [exact Hp|exact Hq|reflexivity].
Qed.

Lemma expression_vacuity_graph M env x p a b v :
  code_relation M env x a -> code_relation M env p b ->
  (code_relation M env (E_vac x p) v <-> vacuity_graph M a b v).
Proof.
  intros Hx Hp. unfold vacuity_graph.
  change (code_relation M env
    (code_subst (x .: p .: fun _ => CEconst 0) (E_vac (CEvar 0) (CEvar 1))) v <->
    code_relation M (a .: b .: fun _ => zeroM M) (E_vac (CEvar 0) (CEvar 1)) v).
  apply code_subst_graph. intros [|[|i]]; [exact Hx|exact Hp|reflexivity].
Qed.

Lemma vacuity_formula_correct M rho x p v :
  holds M rho (vacuity_formula x p v) <->
  vacuity_graph M (evalM M rho x) (evalM M rho p) (evalM M rho v).
Proof.
  unfold vacuity_formula,vacuity_graph. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|i]]; reflexivity.
Qed.

Lemma vacuity_graph_total M x p : exists v, vacuity_graph M x p v.
Proof. apply code_relation_total. Qed.

Lemma vacuity_graph_functional M x p v w :
  vacuity_graph M x p v -> vacuity_graph M x p w -> v=w.
Proof. apply code_relation_functional. Qed.

Theorem numerical_vacuity_implication M env x p q a b v :
  code_relation M env (E_vac x p) a -> code_relation M env (E_vac x q) b ->
  code_relation M env (E_vac x (E_wim p q)) v ->
  numerically_provable M a -> numerically_provable M b -> numerically_provable M v.
Proof.
  intros Ha Hb Hv Hpa Hpb.
  apply (unguarded_macro_sound M env (E_vac x p :: E_vac x q :: nil) (E_vac x (E_wim p q))
    (macro_two_inputs M env _ _ a b Ha Hb Hpa Hpb)); [|exact Hv].
  apply macro_vacuous_implication; apply PM_input; cbn; auto.
Qed.

Theorem numerical_vacuity_universal M env x y p a v :
  code_relation M env (E_vac y p) a ->
  code_relation M env (E_vac y (E_wal x p)) v ->
  numerically_provable M a -> numerically_provable M v.
Proof.
  intros Ha Hv Hpa.
  apply (unguarded_macro_sound M env (E_vac y p :: nil) (E_vac y (E_wal x p))
    (macro_one_input M env _ a Ha Hpa)); [|exact Hv].
  apply macro_vacuous_universal,PM_input. now left.
Qed.

Theorem numerical_vacuity_truth M env x v :
  code_relation M env (E_vac x (CEconst 0)) v -> numerically_provable M v.
Proof.
  intro Hv. apply (unguarded_macro_sound M env nil (E_vac x (CEconst 0))); [| |exact Hv].
  - intros e H. inversion H.
  - eapply PM_mp.
    + apply PM_gen,PM_template,TP_true.
    + apply PM_template,template_K.
Qed.

Print Assumptions numerical_vacuity_implication.
Print Assumptions numerical_vacuity_universal.
Print Assumptions numerical_vacuity_truth.
