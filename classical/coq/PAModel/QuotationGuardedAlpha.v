(** Proof-producing alpha conversion and congruence for the exact guarded
    quantifiers emitted by quotation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent CodeTags
  NumericalProofs NumericalEquivalence FiniteTemplateRebase QuotationPayloads
  QuotationBinderFresh QuotationFormulaFresh QuotationNamedSubstitution
  TemplateNamedSubstitution NamedLeibnizSteps NamedSubstitution NamedBinderFresh
  NamedBinderConstructors FormulaFreshConstructors FreshNames NamedAlpha
  TemplateExistsAlpha ContextualGuardedQuantifiers SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma quotation_guarded_equivalent M universal x t a b f g :
  numerical_equivalent M a b -> quotation_quantifier M universal x t a f ->
  quotation_quantifier M universal x t b g -> numerical_equivalent M f g.
Proof.
  intros HAB HF HG.
  destruct (tagged_pair_total M 1 t x) as [dom HD].
  destruct universal.
  - destruct (quotation_binary_total M SFImpl dom a) as [u HU].
    destruct (quotation_binary_total M SFImpl dom b) as [v HV].
    apply (template_quantified_equivalent M true x u v f g).
    + exact (numerical_equivalent_binary M SFImpl dom a dom b u v
        (numerical_equivalent_refl M dom) HAB HU HV).
    + exact (proj1 (quotation_guarded_all_graph M x t a dom u f HD HU) HF).
    + exact (proj1 (quotation_guarded_all_graph M x t b dom v g HD HV) HG).
  - destruct (quotation_binary_total M SFAnd dom a) as [u HU].
    destruct (quotation_binary_total M SFAnd dom b) as [v HV].
    apply (template_quantified_equivalent M false x u v f g).
    + exact (numerical_equivalent_binary M SFAnd dom a dom b u v
        (numerical_equivalent_refl M dom) HAB HU HV).
    + exact (proj1 (quotation_guarded_exists_graph M x t a dom u f HD HU) HF).
    + exact (proj1 (quotation_guarded_exists_graph M x t b dom v g HD HV) HG).
Qed.

Lemma quotation_guarded_alpha M universal t x y a b f g :
  x<>zeroM M -> y<>zeroM M -> x<>y -> t<>x -> t<>y ->
  named_binder_absent M a x -> formula_fresh M a y -> named_substitution M a x y b ->
  quotation_quantifier M universal x t a f -> quotation_quantifier M universal y t b g ->
  numerical_equivalent M f g.
Proof.
  intros Hx Hy Hxy Htx Hty HA Hfresh HS HF HG.
  destruct (tagged_pair_total M 1 t x) as [dom HD].
  destruct (tagged_pair_total M 1 t y) as [dom' HD'].
  assert (Hdomsub : named_substitution M dom x y dom').
  { apply (ns_combine_atom M false t x dom t y dom' x y HD HD').
    - right;auto.
    - left;auto. }
  assert (Hdomabs : named_binder_absent M dom x).
  { exact (named_binder_absent_membership M t x dom x HD). }
  assert (Hdomfresh : formula_fresh M dom y).
  { exact (formula_fresh_membership_intro M t x dom y HD Hty Hxy). }
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (f .: g .: fun _=>zeroM M)) as [forward Hforward].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (g .: f .: fun _=>zeroM M)) as [backward Hbackward].
  destruct universal.
  - destruct (quotation_binary_total M SFImpl dom a) as [u HU].
    destruct (quotation_binary_total M SFImpl dom' b) as [v HV].
    assert (Huv : named_substitution M u x y v).
    { exact (quotation_binary_named_substitution M SFImpl dom a dom' b u v x y Hx Hdomsub HS HU HV). }
    assert (Habs : named_binder_absent M u x).
    { exact (quotation_binary_binder_absent M SFImpl dom a u x HU Hdomabs HA). }
    assert (Hfr : formula_fresh M u y).
    { exact (quotation_binary_fresh M SFImpl dom a u y HU Hy Hdomfresh Hfresh). }
    destruct (numerical_named_alpha M u x y v f g forward backward Hxy Habs Hfr Huv
      (proj1 (quotation_guarded_all_graph M x t a dom u f HD HU) HF)
      (proj1 (quotation_guarded_all_graph M y t b dom' v g HD' HV) HG)
      Hforward Hbackward) as [PF PB].
    exact (numerical_equivalent_of_proofs M f g forward backward Hforward Hbackward PF PB).
  - destruct (quotation_binary_total M SFAnd dom a) as [u HU].
    destruct (quotation_binary_total M SFAnd dom' b) as [v HV].
    assert (Huv : named_substitution M u x y v).
    { exact (quotation_binary_named_substitution M SFAnd dom a dom' b u v x y Hx Hdomsub HS HU HV). }
    assert (Habs : named_binder_absent M u x).
    { exact (quotation_binary_binder_absent M SFAnd dom a u x HU Hdomabs HA). }
    assert (Hfr : formula_fresh M u y).
    { exact (quotation_binary_fresh M SFAnd dom a u y HU Hy Hdomfresh Hfresh). }
    destruct (numerical_named_exists_alpha M u x y v f g forward backward Hx Hy Hxy Habs Hfr Huv
      (proj1 (quotation_guarded_exists_graph M x t a dom u f HD HU) HF)
      (proj1 (quotation_guarded_exists_graph M y t b dom' v g HD' HV) HG)
      Hforward Hbackward) as [PF PB].
    exact (numerical_equivalent_of_proofs M f g forward backward Hforward Hbackward PF PB).
Qed.

Print Assumptions quotation_guarded_alpha.
