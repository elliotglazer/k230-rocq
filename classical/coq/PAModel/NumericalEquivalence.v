(** Equivalence here means that both implications have internally coded K
    proofs. Congruence constructs such proofs and uses no completeness rule. *)
From PAModel Require Import Model FiniteCoding FiniteCRTFormula CodeExpressions NumericalProofs
  ProofClosure ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  NamedLeibnizSteps NamedAlpha NumericalVacuitySteps QuotationPayloads
  QuotationFixedSource SetFormulaCodes QuotientAtomTemplates.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition numerical_implies M a b :=
  forall f,implication_graph M a b f -> numerically_provable M f.
Definition numerical_equivalent M a b := numerical_implies M a b /\ numerical_implies M b a.
Definition expression_equivalent M rho a b :=
  ns_proof M rho (E_wim a b) /\ ns_proof M rho (E_wim b a).

Lemma numerical_implies_expression M rho a b x y :
  code_relation M rho a x -> code_relation M rho b y ->
  (ns_proof M rho (E_wim a b) <-> numerical_implies M x y).
Proof.
  intros Ha Hb. split;intros HP f Hf;apply HP.
  - exact (proj2 (expression_implication_iff M rho a b x y f Ha Hb) Hf).
  - exact (proj1 (expression_implication_iff M rho a b x y f Ha Hb) Hf).
Qed.

Lemma numerical_equivalent_expression M rho a b x y :
  code_relation M rho a x -> code_relation M rho b y ->
  (expression_equivalent M rho a b <-> numerical_equivalent M x y).
Proof.
  intros Ha Hb. unfold expression_equivalent,numerical_equivalent.
  rewrite (numerical_implies_expression M rho a b x y Ha Hb),
    (numerical_implies_expression M rho b a y x Hb Ha). reflexivity.
Qed.

Lemma expression_equivalent_refl M rho a : expression_equivalent M rho a a.
Proof. split;apply ns_proof_template,template_I. Qed.
Lemma expression_equivalent_sym M rho a b :
  expression_equivalent M rho a b -> expression_equivalent M rho b a.
Proof. intros [Ha Hb]. now split. Qed.
Lemma expression_equivalent_trans M rho a b c :
  expression_equivalent M rho a b -> expression_equivalent M rho b c ->
  expression_equivalent M rho a c.
Proof.
  intros [Hab Hba] [Hbc Hcb]. split.
  - exact (ns_proof_syl M rho a b c Hab Hbc).
  - exact (ns_proof_syl M rho c b a Hcb Hba).
Qed.

Lemma equivalence_implication_macro a a' b b' :
  proof_macro nil (E_wim a' a :: E_wim b b' :: nil) (E_wim (E_wim a b) (E_wim a' b')).
Proof.
  apply macro_discharge,macro_deduction,macro_deduction.
  eapply md_mp with (a:=b).
  - eapply md_mp with (a:=a).
    + eapply md_mp with (a:=a').
      * apply md_hyp;cbn;auto.
      * apply md_global,PM_input;cbn;auto.
    + apply md_hyp;cbn;auto.
  - apply md_global,PM_input;cbn;auto.
Qed.

Lemma expression_implication_monotone M rho a a' b b' :
  ns_proof M rho (E_wim a' a) -> ns_proof M rho (E_wim b b') ->
  ns_proof M rho (E_wim (E_wim a b) (E_wim a' b')).
Proof.
  intros Ha Hb. apply (ns_proof_macro M rho (E_wim a' a :: E_wim b b' :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply equivalence_implication_macro.
Qed.

Lemma expression_equivalent_implication M rho a a' b b' :
  expression_equivalent M rho a a' -> expression_equivalent M rho b b' ->
  expression_equivalent M rho (E_wim a b) (E_wim a' b').
Proof.
  intros [Ha Ha'] [Hb Hb']. split;apply expression_implication_monotone;assumption.
Qed.
Lemma expression_equivalent_negation M rho a a' :
  expression_equivalent M rho a a' -> expression_equivalent M rho (E_wn a) (E_wn a').
Proof.
  intro Ha. apply expression_equivalent_implication;[exact Ha|apply expression_equivalent_refl].
Qed.
Lemma expression_equivalent_conjunction M rho a a' b b' :
  expression_equivalent M rho a a' -> expression_equivalent M rho b b' ->
  expression_equivalent M rho (E_wa a b) (E_wa a' b').
Proof.
  intros Ha Hb. unfold E_wa. apply expression_equivalent_negation.
  apply expression_equivalent_implication;[exact Ha|].
  now apply expression_equivalent_negation.
Qed.
Lemma expression_equivalent_disjunction M rho a a' b b' :
  expression_equivalent M rho a a' -> expression_equivalent M rho b b' ->
  expression_equivalent M rho (E_or a b) (E_or a' b').
Proof.
  intros Ha Hb. unfold E_or. apply expression_equivalent_implication;[|exact Hb].
  now apply expression_equivalent_negation.
Qed.
Lemma expression_equivalent_all M rho x a b :
  expression_equivalent M rho a b ->
  expression_equivalent M rho (E_wal x a) (E_wal x b).
Proof. intros [Ha Hb]. split;now apply ns_proof_all_monotone. Qed.
Lemma expression_equivalent_exists M rho x a b :
  expression_equivalent M rho a b ->
  expression_equivalent M rho (E_wex x a) (E_wex x b).
Proof.
  intros [Ha Hb]. split;apply (ns_proof_macro M rho (E_wim a b :: E_wim b a :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_exists_monotone,PM_input;cbn;auto.
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_exists_monotone,PM_input;cbn;auto.
Qed.

Lemma numerical_equivalent_refl M a : numerical_equivalent M a a.
Proof.
  apply (proj1 (numerical_equivalent_expression M (a .: fun _=>zeroM M)
    (CEvar 0) (CEvar 0) a a eq_refl eq_refl)).
  apply expression_equivalent_refl.
Qed.
Lemma numerical_equivalent_of_proofs M a b p q :
  implication_graph M a b p -> implication_graph M b a q ->
  numerically_provable M p -> numerically_provable M q -> numerical_equivalent M a b.
Proof.
  intros Hp Hq Pp Pq. split;intros f Hf.
  - assert (f=p) by (eapply code_relation_functional;eassumption). now subst f.
  - assert (f=q) by (eapply code_relation_functional;eassumption). now subst f.
Qed.
Lemma numerical_equivalent_sym M a b :
  numerical_equivalent M a b -> numerical_equivalent M b a.
Proof. intros [Ha Hb]. now split. Qed.
Lemma numerical_implies_trans M a b c :
  numerical_implies M a b -> numerical_implies M b c -> numerical_implies M a c.
Proof.
  intros HAB HBC. set (rho:=a .: b .: c .: fun _=>zeroM M).
  apply (proj1 (numerical_implies_expression M rho (CEvar 0) (CEvar 2) a c eq_refl eq_refl)).
  apply (ns_proof_syl M rho (CEvar 0) (CEvar 1) (CEvar 2)).
  - exact (proj2 (numerical_implies_expression M rho (CEvar 0) (CEvar 1) a b eq_refl eq_refl) HAB).
  - exact (proj2 (numerical_implies_expression M rho (CEvar 1) (CEvar 2) b c eq_refl eq_refl) HBC).
Qed.
Lemma numerical_implies_apply M a b :
  numerical_implies M a b -> numerically_provable M a -> numerically_provable M b.
Proof.
  intros HAB HA. destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (a .: b .: fun _=>zeroM M)) as [f HF].
  exact (numerical_mp M a b f HA (HAB f HF) HF).
Qed.
Lemma numerical_equivalent_trans M a b c :
  numerical_equivalent M a b -> numerical_equivalent M b c -> numerical_equivalent M a c.
Proof.
  intros Hab Hbc. set (rho:=a .: b .: c .: fun _=>zeroM M).
  apply (proj1 (numerical_equivalent_expression M rho (CEvar 0) (CEvar 2) a c eq_refl eq_refl)).
  apply (expression_equivalent_trans M rho (CEvar 0) (CEvar 1) (CEvar 2)).
  - exact (proj2 (numerical_equivalent_expression M rho (CEvar 0) (CEvar 1) a b eq_refl eq_refl) Hab).
  - exact (proj2 (numerical_equivalent_expression M rho (CEvar 1) (CEvar 2) b c eq_refl eq_refl) Hbc).
Qed.

Lemma numerical_equivalent_binary M h a b a' b' f g :
  numerical_equivalent M a a' -> numerical_equivalent M b b' ->
  quotation_binary M h a b f -> quotation_binary M h a' b' g -> numerical_equivalent M f g.
Proof.
  intros Ha Hb Hf Hg. set (rho:=a .: b .: a' .: b' .: fun _=>zeroM M).
  assert (HA : expression_equivalent M rho (CEvar 0) (CEvar 2)).
  { exact (proj2 (numerical_equivalent_expression M rho (CEvar 0) (CEvar 2) a a' eq_refl eq_refl) Ha). }
  assert (HB : expression_equivalent M rho (CEvar 1) (CEvar 3)).
  { exact (proj2 (numerical_equivalent_expression M rho (CEvar 1) (CEvar 3) b b' eq_refl eq_refl) Hb). }
  pose proof (proj2 (quotation_binary_substitution_graph M rho h
    (CEvar 0) (CEvar 1) a b f eq_refl eq_refl) Hf) as EF.
  pose proof (proj2 (quotation_binary_substitution_graph M rho h
    (CEvar 2) (CEvar 3) a' b' g eq_refl eq_refl) Hg) as EG.
  apply (proj1 (numerical_equivalent_expression M rho _ _ f g EF EG)).
  destruct h;cbn [quotation_binary_expression code_subst];
    first [apply expression_equivalent_conjunction|apply expression_equivalent_disjunction|
      apply expression_equivalent_implication];assumption.
Qed.

Print Assumptions numerical_equivalent_trans.
Print Assumptions numerical_equivalent_binary.

#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition numerical_implies_formula (a b : term) : form :=
  ∀ (implication_formula a`[↑] b`[↑] $0 → numerically_provable_formula $0).
Definition numerical_equivalent_formula (a b : term) : form :=
  numerical_implies_formula a b ∧ numerical_implies_formula b a.
Local Opaque holds implication_formula numerically_provable_formula.
Lemma numerical_implies_formula_correct M rho a b :
  holds M rho (numerical_implies_formula a b) <->
  numerical_implies M (evalM M rho a) (evalM M rho b).
Proof.
  unfold numerical_implies_formula,numerical_implies.
  rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite implication_formula_correct. setoid_rewrite numerically_provable_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Lemma numerical_equivalent_formula_correct M rho a b :
  holds M rho (numerical_equivalent_formula a b) <->
  numerical_equivalent M (evalM M rho a) (evalM M rho b).
Proof.
  unfold numerical_equivalent_formula,numerical_equivalent.
  rewrite holds_and,!numerical_implies_formula_correct. reflexivity.
Qed.
