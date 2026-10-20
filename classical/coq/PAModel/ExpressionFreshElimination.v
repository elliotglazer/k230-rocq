(** Freshness elimination for expression constructors, including a zero
    implication. The zero case has zero children, which mention no names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs FreshNames FreshPropagation FormulaFreshConstructors
  NumericalMatrixPadding TemplateFormulaFresh ProofTemplates NumericalEquality
  QuotientAtomTemplates.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma fresh_implication_parts M a b f x :
  implication_graph M a b f -> formula_fresh M f x ->
  formula_fresh M a x /\ formula_fresh M b x.
Proof.
  intros H HF.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) f (zeroM M)) as [E|Hnz].
  - subst f. destruct (padding_zero_implication_inputs M a b H) as [-> ->].
    split;apply formula_fresh_zero.
  - exact (formula_fresh_implication M a b f x Hnz H HF).
Qed.

Lemma expression_fresh_implication_parts M rho x A B :
  expression_fresh M rho x (E_wim A B) ->
  expression_fresh M rho x A /\ expression_fresh M rho x B.
Proof.
  intro HF. split.
  - intros a HA. destruct (code_relation_total M B rho) as [b HB].
    destruct (code_relation_total M (E_wim A B) rho) as [f Hf].
    exact (proj1 (fresh_implication_parts M a b f x
      (expression_implication_graph M rho A B a b f HA HB Hf) (HF f Hf))).
  - intros b HB. destruct (code_relation_total M A rho) as [a HA].
    destruct (code_relation_total M (E_wim A B) rho) as [f Hf].
    exact (proj2 (fresh_implication_parts M a b f x
      (expression_implication_graph M rho A B a b f HA HB Hf) (HF f Hf))).
Qed.

Lemma expression_fresh_negation_body M rho x A :
  expression_fresh M rho x (E_wn A) -> expression_fresh M rho x A.
Proof. intro HF. exact (proj1 (expression_fresh_implication_parts M rho x A (CEconst 1) HF)). Qed.

Lemma expression_fresh_conjunction_parts M rho x A B :
  expression_fresh M rho x (E_wa A B) ->
  expression_fresh M rho x A /\ expression_fresh M rho x B.
Proof.
  intro HF. apply expression_fresh_negation_body in HF.
  destruct (expression_fresh_implication_parts M rho x A (E_wn B) HF) as [HA HB].
  split;[exact HA|now apply expression_fresh_negation_body in HB].
Qed.

Lemma expression_fresh_disjunction_parts M rho x A B :
  expression_fresh M rho x (E_or A B) ->
  expression_fresh M rho x A /\ expression_fresh M rho x B.
Proof.
  intro HF. destruct (expression_fresh_implication_parts M rho x (E_wn A) B HF) as [HA HB].
  split;[now apply expression_fresh_negation_body in HA|exact HB].
Qed.

Lemma expression_fresh_equality_names M rho x A B :
  expression_fresh M rho x (E_weq A B) ->
  expression_name_avoids M rho x A /\ expression_name_avoids M rho x B.
Proof.
  intro HF. split.
  - intros a HA. destruct (code_relation_total M B rho) as [b HB].
    destruct (code_relation_total M (E_weq A B) rho) as [f Hf].
    exact (proj1 (formula_fresh_equality M a b f x
      (proj1 (expression_equality_graph M rho A B a b f HA HB) Hf) (HF f Hf))).
  - intros b HB. destruct (code_relation_total M A rho) as [a HA].
    destruct (code_relation_total M (E_weq A B) rho) as [f Hf].
    exact (proj2 (formula_fresh_equality M a b f x
      (proj1 (expression_equality_graph M rho A B a b f HA HB) Hf) (HF f Hf))).
Qed.

Lemma expression_fresh_universal_parts M rho x X A :
  expression_fresh M rho x (E_wal X A) ->
  expression_name_avoids M rho x X /\ expression_fresh M rho x A.
Proof.
  intro HF. split.
  - intros a HA. destruct (code_relation_total M A rho) as [b HB].
    destruct (code_relation_total M (E_wal X A) rho) as [f Hf].
    exact (proj1 (formula_fresh_universal M a b f x
      (expression_universal_graph M rho X A a b f HA HB Hf) (HF f Hf))).
  - intros b HB. destruct (code_relation_total M X rho) as [a HA].
    destruct (code_relation_total M (E_wal X A) rho) as [f Hf].
    exact (proj2 (formula_fresh_universal M a b f x
      (expression_universal_graph M rho X A a b f HA HB Hf) (HF f Hf))).
Qed.

Print Assumptions fresh_implication_parts.
Print Assumptions expression_fresh_conjunction_parts.
Print Assumptions expression_fresh_universal_parts.
