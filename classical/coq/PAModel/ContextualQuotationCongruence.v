(** Logical constructor congruence for numerical quotient quotation under
    local assumptions. The atom case is separate. Quantifier congruence
    requires the allocated name to be fresh for the actual context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent CodeTags
  NumericalProofs ProofTemplates ContextualProofs ContextualEquivalence
  NumericalEquivalence QuotationPayloads QuotationFixedSource QuotientAtomTemplates
  SetFormulaCodes FiniteTemplateEvaluation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem contextual_equivalence_binary M cb cc cn h a b a' b' f g :
  contextual_equivalence M cb cc cn a a' ->
  contextual_equivalence M cb cc cn b b' ->
  quotation_binary M h a b f -> quotation_binary M h a' b' g ->
  contextual_equivalence M cb cc cn f g.
Proof.
  intros Ha Hb Hf Hg. set (rho:=a .: b .: a' .: b' .: fun _=>zeroM M).
  assert (HA : contextual_expression_equivalence M cb cc cn rho (CEvar 0) (CEvar 2)).
  { exact (proj2 (contextual_equivalence_expression M cb cc cn rho
      (CEvar 0) (CEvar 2) a a' eq_refl eq_refl) Ha). }
  assert (HB : contextual_expression_equivalence M cb cc cn rho (CEvar 1) (CEvar 3)).
  { exact (proj2 (contextual_equivalence_expression M cb cc cn rho
      (CEvar 1) (CEvar 3) b b' eq_refl eq_refl) Hb). }
  pose proof (proj2 (quotation_binary_substitution_graph M rho h
    (CEvar 0) (CEvar 1) a b f eq_refl eq_refl) Hf) as EF.
  pose proof (proj2 (quotation_binary_substitution_graph M rho h
    (CEvar 2) (CEvar 3) a' b' g eq_refl eq_refl) Hg) as EG.
  apply (proj1 (contextual_equivalence_expression M cb cc cn rho _ _ f g EF EG)).
  destruct h;cbn [quotation_binary_expression code_subst];
    first [apply contextual_expression_equivalence_conjunction|
      apply contextual_expression_equivalence_disjunction|
      apply contextual_expression_equivalence_implication];assumption.
Qed.

Theorem contextual_equivalence_quantified M cb cc cn universal x a b f g :
  context_fresh M cb cc cn x -> contextual_equivalence M cb cc cn a b ->
  template_quantified M universal x a f -> template_quantified M universal x b g ->
  contextual_equivalence M cb cc cn f g.
Proof.
  intros HX HAB HF HG. set (rho:=x .: a .: b .: fun _=>zeroM M).
  assert (HE : contextual_expression_equivalence M cb cc cn rho (CEvar 1) (CEvar 2)).
  { exact (proj2 (contextual_equivalence_expression M cb cc cn rho
      (CEvar 1) (CEvar 2) a b eq_refl eq_refl) HAB). }
  destruct universal.
  - apply (proj1 (contextual_equivalence_expression M cb cc cn rho
      (E_wal (CEvar 0) (CEvar 1)) (E_wal (CEvar 0) (CEvar 2)) f g
      (proj2 (template_quantified_graph M rho true (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF)
      (proj2 (template_quantified_graph M rho true (CEvar 0) (CEvar 2) x b g eq_refl eq_refl) HG))).
    exact (contextual_expression_equivalence_all M cb cc cn rho
      (CEvar 0) (CEvar 1) (CEvar 2) x eq_refl HX HE).
  - apply (proj1 (contextual_equivalence_expression M cb cc cn rho
      (E_wex (CEvar 0) (CEvar 1)) (E_wex (CEvar 0) (CEvar 2)) f g
      (proj2 (template_quantified_graph M rho false (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF)
      (proj2 (template_quantified_graph M rho false (CEvar 0) (CEvar 2) x b g eq_refl eq_refl) HG))).
    exact (contextual_expression_equivalence_exists M cb cc cn rho
      (CEvar 0) (CEvar 1) (CEvar 2) x eq_refl HX HE).
Qed.

Theorem contextual_equivalence_guarded M cb cc cn universal x t a b f g :
  context_fresh M cb cc cn x -> contextual_equivalence M cb cc cn a b ->
  quotation_quantifier M universal x t a f -> quotation_quantifier M universal x t b g ->
  contextual_equivalence M cb cc cn f g.
Proof.
  intros HX HAB HF HG. set (rho:=x .: t .: a .: b .: fun _=>zeroM M).
  assert (HE : contextual_expression_equivalence M cb cc cn rho (CEvar 2) (CEvar 3)).
  { exact (proj2 (contextual_equivalence_expression M cb cc cn rho
      (CEvar 2) (CEvar 3) a b eq_refl eq_refl) HAB). }
  assert (EF : code_relation M rho
    (code_subst (code_parameters (CEvar 0) (CEvar 1) (CEvar 2) (CEconst 0))
      (quotation_quantifier_expression universal)) f).
  { apply (proj2 (code_subst_graph M rho
      (code_parameters (CEvar 0) (CEvar 1) (CEvar 2) (CEconst 0))
      (code_parameters x t a (zeroM M))
      ltac:(intros [|[|[|i]]];reflexivity) _ f)). exact HF. }
  assert (EG : code_relation M rho
    (code_subst (code_parameters (CEvar 0) (CEvar 1) (CEvar 3) (CEconst 0))
      (quotation_quantifier_expression universal)) g).
  { apply (proj2 (code_subst_graph M rho
      (code_parameters (CEvar 0) (CEvar 1) (CEvar 3) (CEconst 0))
      (code_parameters x t b (zeroM M))
      ltac:(intros [|[|[|i]]];reflexivity) _ g)). exact HG. }
  apply (proj1 (contextual_equivalence_expression M cb cc cn rho _ _ f g EF EG)).
  destruct universal;cbn [quotation_quantifier_expression code_subst code_parameters].
  - apply (contextual_expression_equivalence_all M cb cc cn rho (CEvar 0) _ _ x eq_refl HX).
    apply contextual_expression_equivalence_implication;
      [apply contextual_expression_equivalence_refl|exact HE].
  - apply (contextual_expression_equivalence_exists M cb cc cn rho (CEvar 0) _ _ x eq_refl HX).
    apply contextual_expression_equivalence_conjunction;
      [apply contextual_expression_equivalence_refl|exact HE].
Qed.

Print Assumptions contextual_equivalence_binary.
Print Assumptions contextual_equivalence_quantified.
Print Assumptions contextual_equivalence_guarded.
