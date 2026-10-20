(** Congruence under an internally coded local context. Quantifier
    congruence retains the context-freshness premise needed by its actual
    generalization step. These lemmas do not weaken arbitrary contexts. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates TemplatePropositional QuantifierMacros NumericalVacuitySteps
  NumericalEquivalence NamedLeibnizSteps ContextualProofs ContextualLogic ContextualPropositional
  NumericalContexts NumericalEnvironments QuotientAtomTemplates.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition contextual_implies M b c n a d := forall f,
  implication_graph M a d f -> contextually_provable M b c n f.
Definition contextual_equivalence M b c n a d :=
  contextual_implies M b c n a d /\ contextual_implies M b c n d a.
Definition contextual_expression M b c n rho e := forall f,
  code_relation M rho e f -> contextually_provable M b c n f.
Definition contextual_expression_equivalence M b c n rho a d :=
  contextual_expression M b c n rho (E_wim a d) /\
  contextual_expression M b c n rho (E_wim d a).

Definition contextual_implies_formula (b c n a d : term) : form :=
  ∀ (implication_formula a`[↑] d`[↑] $0 →
    contextually_provable_formula b`[↑] c`[↑] n`[↑] $0).
Definition contextual_equivalence_formula (b c n a d : term) : form :=
  contextual_implies_formula b c n a d ∧ contextual_implies_formula b c n d a.

Local Opaque holds implication_formula contextually_provable_formula.
Lemma contextual_implies_formula_correct M rho b c n a d :
  holds M rho (contextual_implies_formula b c n a d) <->
  contextual_implies M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho a) (evalM M rho d).
Proof.
  unfold contextual_implies_formula,contextual_implies.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite implication_formula_correct.
  setoid_rewrite contextually_provable_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Lemma contextual_equivalence_formula_correct M rho b c n a d :
  holds M rho (contextual_equivalence_formula b c n a d) <->
  contextual_equivalence M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho a) (evalM M rho d).
Proof.
  unfold contextual_equivalence_formula,contextual_equivalence.
  rewrite holds_and,!contextual_implies_formula_correct. reflexivity.
Qed.

Lemma contextual_implies_expression M b c n rho a d x y :
  code_relation M rho a x -> code_relation M rho d y ->
  (contextual_expression M b c n rho (E_wim a d) <->
    contextual_implies M b c n x y).
Proof.
  intros HA HD. split;intros HP f HF;apply HP.
  - exact (proj2 (expression_implication_iff M rho a d x y f HA HD) HF).
  - exact (proj1 (expression_implication_iff M rho a d x y f HA HD) HF).
Qed.
Lemma contextual_equivalence_expression M b c n rho a d x y :
  code_relation M rho a x -> code_relation M rho d y ->
  (contextual_expression_equivalence M b c n rho a d <->
    contextual_equivalence M b c n x y).
Proof.
  intros HA HD. unfold contextual_expression_equivalence,contextual_equivalence.
  rewrite (contextual_implies_expression M b c n rho a d x y HA HD),
    (contextual_implies_expression M b c n rho d a y x HD HA). reflexivity.
Qed.

Lemma contextual_expression_global M b c n rho e :
  ns_proof M rho e -> contextual_expression M b c n rho e.
Proof. intros HP f HF. apply contextual_global,HP,HF. Qed.
Lemma contextual_expression_template M b c n rho e :
  template_proof nil e -> contextual_expression M b c n rho e.
Proof. intros HP f HF. exact (contextual_template M b c n rho e f HP HF). Qed.
Lemma contextual_expression_mp M b c n rho a d :
  contextual_expression M b c n rho a ->
  contextual_expression M b c n rho (E_wim a d) ->
  contextual_expression M b c n rho d.
Proof.
  intros PA PAD f HF. destruct (code_relation_total M a rho) as [x HX].
  destruct (code_relation_total M (E_wim a d) rho) as [h HH].
  exact (contextual_mp_expression M b c n rho a d x f h HX HF HH (PA x HX) (PAD h HH)).
Qed.
Lemma contextual_expression_derivation M b c n rho inputs e :
  (forall d,In d inputs -> contextual_expression M b c n rho d) ->
  template_derivation nil inputs e -> contextual_expression M b c n rho e.
Proof.
  intros HI HD f HF. apply (contextual_propositional_sound M b c n rho inputs e);
    [exact HI|exact HD|exact HF].
Qed.

Lemma contextual_expression_equivalence_refl M b c n rho a :
  contextual_expression_equivalence M b c n rho a a.
Proof. split;apply contextual_expression_template,template_I. Qed.
Lemma contextual_expression_equivalence_sym M b c n rho a d :
  contextual_expression_equivalence M b c n rho a d ->
  contextual_expression_equivalence M b c n rho d a.
Proof. intros [HA HD]. now split. Qed.

Lemma contextual_implication_program a a' d d' :
  template_derivation nil (E_wim a' a :: E_wim d d' :: nil)
    (E_wim (E_wim a d) (E_wim a' d')).
Proof.
  do 2 apply template_deduction.
  eapply dmp with (a:=d);[apply dhyp;cbn;tauto|].
  eapply dmp with (a:=a);[apply dhyp;cbn;tauto|].
  eapply dmp with (a:=a');apply dhyp;cbn;tauto.
Qed.
Lemma contextual_expression_implication_monotone M b c n rho a a' d d' :
  contextual_expression M b c n rho (E_wim a' a) ->
  contextual_expression M b c n rho (E_wim d d') ->
  contextual_expression M b c n rho (E_wim (E_wim a d) (E_wim a' d')).
Proof.
  intros HA HD. apply (contextual_expression_derivation M b c n rho
    (E_wim a' a :: E_wim d d' :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply contextual_implication_program.
Qed.
Lemma contextual_expression_equivalence_implication M b c n rho a a' d d' :
  contextual_expression_equivalence M b c n rho a a' ->
  contextual_expression_equivalence M b c n rho d d' ->
  contextual_expression_equivalence M b c n rho (E_wim a d) (E_wim a' d').
Proof.
  intros [HA HA'] [HD HD']. split;apply contextual_expression_implication_monotone;assumption.
Qed.
Lemma contextual_expression_equivalence_negation M b c n rho a a' :
  contextual_expression_equivalence M b c n rho a a' ->
  contextual_expression_equivalence M b c n rho (E_wn a) (E_wn a').
Proof.
  intro HA. apply contextual_expression_equivalence_implication;
    [exact HA|apply contextual_expression_equivalence_refl].
Qed.
Lemma contextual_expression_equivalence_conjunction M b c n rho a a' d d' :
  contextual_expression_equivalence M b c n rho a a' ->
  contextual_expression_equivalence M b c n rho d d' ->
  contextual_expression_equivalence M b c n rho (E_wa a d) (E_wa a' d').
Proof.
  intros HA HD. unfold E_wa. apply contextual_expression_equivalence_negation.
  apply contextual_expression_equivalence_implication;[exact HA|].
  now apply contextual_expression_equivalence_negation.
Qed.
Lemma contextual_expression_equivalence_disjunction M b c n rho a a' d d' :
  contextual_expression_equivalence M b c n rho a a' ->
  contextual_expression_equivalence M b c n rho d d' ->
  contextual_expression_equivalence M b c n rho (E_or a d) (E_or a' d').
Proof.
  intros HA HD. unfold E_or. apply contextual_expression_equivalence_implication;
    [now apply contextual_expression_equivalence_negation|exact HD].
Qed.

Lemma contextual_expression_all_monotone M b c n rho x a d v :
  code_relation M rho x v -> context_fresh M b c n v ->
  contextual_expression M b c n rho (E_wim a d) ->
  contextual_expression M b c n rho (E_wim (E_wal x a) (E_wal x d)).
Proof.
  intros HX HFresh HP.
  assert (HAll : contextual_expression M b c n rho (E_wal x (E_wim a d))).
  { intros f HF. destruct (code_relation_total M (E_wim a d) rho) as [g HG].
    apply (contextual_gen M b c n v g f HFresh (HP g HG)).
    exact (expression_universal_graph M rho x (E_wim a d) v g f HX HG HF). }
  apply (contextual_expression_mp M b c n rho (E_wal x (E_wim a d)));[exact HAll|].
  apply contextual_expression_template,template_r2.
Qed.
Lemma contextual_expression_equivalence_all M b c n rho x a d v :
  code_relation M rho x v -> context_fresh M b c n v ->
  contextual_expression_equivalence M b c n rho a d ->
  contextual_expression_equivalence M b c n rho (E_wal x a) (E_wal x d).
Proof.
  intros HX HF [HA HD]. split.
  - exact (contextual_expression_all_monotone M b c n rho x a d v HX HF HA).
  - exact (contextual_expression_all_monotone M b c n rho x d a v HX HF HD).
Qed.
Lemma contextual_expression_equivalence_exists M b c n rho x a d v :
  code_relation M rho x v -> context_fresh M b c n v ->
  contextual_expression_equivalence M b c n rho a d ->
  contextual_expression_equivalence M b c n rho (E_wex x a) (E_wex x d).
Proof.
  intros HX HF HA. unfold E_wex.
  apply contextual_expression_equivalence_negation.
  apply (contextual_expression_equivalence_all M b c n rho x _ _ v HX HF).
  now apply contextual_expression_equivalence_negation.
Qed.

Theorem contextual_equivalence_global M b c n a d :
  numerical_equivalent M a d -> contextual_equivalence M b c n a d.
Proof. intros [HA HD]. split;intros f HF;apply contextual_global;[apply HA|apply HD];exact HF. Qed.
Theorem contextual_equivalence_apply M b c n a d :
  contextual_equivalence M b c n a d -> contextually_provable M b c n a ->
  contextually_provable M b c n d.
Proof.
  intros [HA _] PA. destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 a d (zeroM M))) as [f HF].
  exact (contextual_mp M b c n a d f PA (HA f HF) HF).
Qed.

Print Assumptions contextual_equivalence_formula_correct.
Print Assumptions contextual_expression_equivalence_implication.
Print Assumptions contextual_expression_equivalence_all.
Print Assumptions contextual_expression_equivalence_exists.
Print Assumptions contextual_equivalence_apply.
