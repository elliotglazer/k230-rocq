(** The four finite raw laws instantiated at arbitrary model-valued names. *)
From RawLogic Require Import RawLogicCertificates.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  ProofTemplates NamedLeibnizSteps NumericalEquivalence RawLawTemplates
  FiniteTemplateSpecialization FiniteTemplateInstantiation FiniteTemplateEvaluation
  FiniteTemplateRebase QuotientAtomTemplates.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_arguments law : list code_expr :=
  match law with RawSymmetry=>[CEvar 1;CEvar 2;CEvar 3] | _=>[CEvar 1;CEvar 2;CEvar 3;CEvar 4] end.
Definition raw_body_environment law := template_bind_arguments (raw_arguments law) (fun _=>CEconst 0).
Definition raw_values M law (t a b c:carrier M) :=
  match law with RawSymmetry=>b .: a .: t .: (fun _=>zeroM M)
  | _=>c .: b .: a .: t .: (fun _=>zeroM M) end.
Definition raw_parameters M (k t a b c:carrier M) := k .: t .: a .: b .: c .: (fun _=>zeroM M).

Lemma raw_prefix_exact law :
  current_raw_source law = template_all_prefix (length (raw_arguments law)) (current_raw_body law).
Proof. destruct law;reflexivity. Qed.

Lemma raw_body_environment_graph M law k t a b c :
  forall idx,code_relation M (raw_parameters M k t a b c) (raw_body_environment law idx)
    (raw_values M law t a b c idx).
Proof.
  destruct law;intros [|[|[|[|idx]]]];reflexivity.
Qed.

Lemma raw_values_below M law k t a b c :
  coding_lt M (zeroM M) k -> coding_lt M t k -> coding_lt M a k ->
  coding_lt M b k -> coding_lt M c k ->
  forall idx,coding_lt M (raw_values M law t a b c idx) k.
Proof. intros H0 Ht Ha Hb Hc. destruct law;intros [|[|[|[|idx]]]];assumption. Qed.

Lemma raw_argument_graphs_below M law k t a b c :
  coding_lt M t k -> coding_lt M a k -> coding_lt M b k -> coding_lt M c k ->
  forall e,In e (raw_arguments law) ->
  exists y,code_relation M (raw_parameters M k t a b c) e y /\ coding_lt M y k.
Proof.
  intros Ht Ha Hb Hc. destruct law;cbn [raw_arguments List.In];
    intros e H;repeat destruct H as [H|H];try contradiction;subst e;
    first [solve [exists t;split;[reflexivity|exact Ht]]
          |solve [exists a;split;[reflexivity|exact Ha]]
          |solve [exists b;split;[reflexivity|exact Hb]]
          |solve [exists c;split;[reflexivity|exact Hc]]].
Qed.

Theorem raw_high_instance_proved law M k t a b c :
  coding_lt M (zeroM M) k -> coding_lt M t k -> coding_lt M a k ->
  coding_lt M b k -> coding_lt M c k ->
  ns_proof M (raw_parameters M k t a b c)
    (template_set_formula (raw_body_environment law)
      (template_advance_fresh (CEvar 0) (length (raw_arguments law)))
      (current_raw_body law)).
Proof.
  intros H0 Ht Ha Hb Hc.
  apply (finite_template_specialize_list M (current_raw_body law) (raw_arguments law)
    (raw_parameters M k t a b c) (fun _=>CEconst 0) (fun _=>zeroM M) (CEvar 0) k).
  - intro idx;reflexivity.
  - intro idx;exact H0.
  - reflexivity.
  - exact H0.
  - exact (raw_argument_graphs_below M law k t a b c Ht Ha Hb Hc).
  - rewrite <- raw_prefix_exact. apply (raw_closed_template_proved law M _ _ k);[reflexivity|exact H0].
Qed.

Theorem raw_body_template_proved law M k t a b c :
  coding_lt M (zeroM M) k -> coding_lt M t k -> coding_lt M a k ->
  coding_lt M b k -> coding_lt M c k ->
  ns_proof M (raw_parameters M k t a b c)
    (template_set_formula (raw_body_environment law) (CEvar 0) (current_raw_body law)).
Proof.
  intros H0 Ht Ha Hb Hc f HF.
  set (rho:=raw_parameters M k t a b c).
  set (eta:=raw_values M law t a b c).
  set (n:=length (raw_arguments law)).
  set (high:=template_advance_name M k n).
  destruct (code_relation_total M
    (template_set_formula (raw_body_environment law)
      (template_advance_fresh (CEvar 0) n) (current_raw_body law)) rho) as [g HG].
  assert (HH : template_hygienic M (current_raw_body law) eta high).
  { apply template_hygienic_below.
    - exact (template_advance_name_above M n (zeroM M) k H0).
    - intro idx;apply template_advance_name_above.
      exact (raw_values_below M law k t a b c H0 Ht Ha Hb Hc idx). }
  assert (HL : template_hygienic M (current_raw_body law) eta k).
  { apply template_hygienic_below;[exact H0|].
    exact (raw_values_below M law k t a b c H0 Ht Ha Hb Hc). }
  assert (EG : template_evaluation M (current_raw_body law) eta high g).
  { apply (proj1 (template_evaluation_graph M (current_raw_body law)
      (raw_body_environment law) (template_advance_fresh (CEvar 0) n) rho eta high g
      (raw_body_environment_graph M law k t a b c)
      (template_advance_fresh_graph M n rho (CEvar 0) k eq_refl))). exact HG. }
  assert (EF : template_evaluation M (current_raw_body law) eta k f).
  { apply (proj1 (template_evaluation_graph M (current_raw_body law)
      (raw_body_environment law) (CEvar 0) rho eta k f
      (raw_body_environment_graph M law k t a b c) eq_refl)). exact HF. }
  apply (numerical_implies_apply M g f).
  - exact (proj1 (finite_template_rebase M (current_raw_body law) eta high k g f HH HL EG EF)).
  - exact (raw_high_instance_proved law M k t a b c H0 Ht Ha Hb Hc g HG).
Qed.

Print Assumptions raw_prefix_exact.
Print Assumptions raw_high_instance_proved.
Print Assumptions raw_body_template_proved.
