(** Finite quantifier proof programs. Inputs are already proved formulas;
    these programs can therefore generalize them. No semantic consequence
    or completeness theorem is used. *)
From PAModel Require Import CodeExpressions ProofTemplates TemplateCD
  TemplatePropositional ProofMacros.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac hyp := apply dhyp; cbn; tauto.

Lemma template_contraposition G p q : template_proof G
  (E_wim (E_wim p q) (E_wim (E_wn q) (E_wn p))).
Proof.
  apply template_discharge. do 3 apply template_deduction.
  unfold E_wn. apply (dmp G _ q); [hyp|]. apply (dmp G _ p); hyp.
Qed.

Lemma template_negative_implication G p q :
  template_proof G (E_wim (E_wn p) (E_wim p q)).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  apply (dmp G _ (CEconst 1)); [apply dthm,template_F|].
  apply (dmp G _ p); hyp.
Qed.

Lemma template_cases_implication G p q x : template_proof G
  (E_wim (E_wim (E_wn p) x) (E_wim (E_wim q x) (E_wim (E_wim p q) x))).
Proof.
  apply template_discharge. do 3 apply template_deduction.
  apply (dmp G _ (E_wn (E_wn x))); [apply dthm,template_DNE|].
  apply template_deduction.
  apply (dmp G _ x); [hyp|]. apply (dmp G _ (E_wn p)); [hyp|].
  apply (dmp G _ (E_wn q)).
  - apply (dmp G _ (E_wim p q)); [apply dthm,template_contraposition|hyp].
  - apply (dmp G _ (E_wn x)).
    + apply (dmp G _ (E_wim q x)); [apply dthm,template_contraposition|hyp].
    + hyp.
Qed.

Section Programs.
Variable G : list (code_expr * code_expr).
Variable Inputs : list code_expr.

Lemma macro_syl p q r : proof_macro G Inputs (E_wim p q) ->
  proof_macro G Inputs (E_wim q r) -> proof_macro G Inputs (E_wim p r).
Proof.
  intros Hpq Hqr.
  exact (PM_mp _ _ Hqr (PM_mp _ _ Hpq (PM_template _ (@template_B G p q r)))).
Qed.

Lemma macro_contra p q : proof_macro G Inputs (E_wim p q) ->
  proof_macro G Inputs (E_wim (E_wn q) (E_wn p)).
Proof. intro H. exact (PM_mp _ _ H (PM_template _ (template_contraposition G p q))). Qed.

Lemma macro_all_monotone x p q : proof_macro G Inputs (E_wim p q) ->
  proof_macro G Inputs (E_wim (E_wal x p) (E_wal x q)).
Proof. intro H. exact (PM_mp _ _ (PM_gen x _ H) (PM_template _ (template_r2 x p q))). Qed.

Lemma macro_exists_monotone x p q : proof_macro G Inputs (E_wim p q) ->
  proof_macro G Inputs (E_wim (E_wex x p) (E_wex x q)).
Proof.
  intro H. unfold E_wex. apply macro_contra,macro_all_monotone,macro_contra,H.
Qed.

Lemma macro_vacuous_negation x p : proof_macro G Inputs (E_wim p (E_wal x p)) ->
  proof_macro G Inputs (E_wim (E_wn p) (E_wal x (E_wn p))).
Proof.
  intro H.
  pose proof (macro_contra _ _ (PM_template _ (@template_r6 G x p))) as H1.
  assert (H2 : proof_macro G Inputs
    (E_wim (E_wn p) (E_wal x (E_wn (E_wal x p))))).
  { eapply macro_syl; [exact H1|]. apply PM_template,template_DNE. }
  eapply macro_syl; [exact H2|]. apply macro_all_monotone,macro_contra,H.
Qed.

Lemma macro_vacuous_implication x p q :
  proof_macro G Inputs (E_wim p (E_wal x p)) ->
  proof_macro G Inputs (E_wim q (E_wal x q)) ->
  proof_macro G Inputs (E_wim (E_wim p q) (E_wal x (E_wim p q))).
Proof.
  intros Hp Hq. set (out := E_wal x (E_wim p q)).
  assert (Hneg : proof_macro G Inputs (E_wim (E_wn p) out)).
  { eapply macro_syl; [apply macro_vacuous_negation,Hp|].
    apply macro_all_monotone,PM_template,template_negative_implication. }
  assert (Hpos : proof_macro G Inputs (E_wim q out)).
  { eapply macro_syl; [exact Hq|]. apply macro_all_monotone,PM_template,template_K. }
  exact (PM_mp _ _ Hpos (PM_mp _ _ Hneg (PM_template _ (template_cases_implication G p q out)))).
Qed.

Lemma macro_vacuous_universal x y p :
  proof_macro G Inputs (E_wim p (E_wal y p)) ->
  proof_macro G Inputs (E_wim (E_wal x p) (E_wal y (E_wal x p))).
Proof.
  intro H. eapply macro_syl; [apply macro_all_monotone;exact H|].
  exact (PM_template _ (TP_row LR4 x y p (CEconst 0))).
Qed.
End Programs.

Print Assumptions template_cases_implication.
Print Assumptions macro_vacuous_negation.
Print Assumptions macro_vacuous_implication.
Print Assumptions macro_vacuous_universal.
