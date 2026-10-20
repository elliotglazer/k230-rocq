(** Named substitution through quotation with interval exclusions, including
    replacement names above the old allocation base. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  CodeDescent SetFormulaCodes SetCodeDescent NumericalEnvironments
  NamedSubstitutionRules NamedSubstitution TemplateNamedSubstitution
  TemplateNamedExclusions TemplateBinderRange FiniteTemplateEvaluation QuotientAtomTemplates
  QuotationPayloads QuotationRules NumericalQuotation QuotationFunctionality
  QuotationNamedSubstitution QuotationAllocationBounds QuotationAtomRebase
  QuotationFormulaFresh FreshNames.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma template_evaluation_substitution M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta eta' k x y v w :
  x<>zeroM M -> template_allocations_avoid M phi k x -> template_allocations_avoid M phi k y ->
  (forall i,named_replace M x y (eta i) (eta' i)) ->
  template_evaluation M phi eta k v -> template_evaluation M phi eta' k w ->
  named_substitution M v x y w.
Proof.
  intros Hx HX HY HE HV HW.
  apply (template_set_formula_named_substitution_exclusions M phi
    template_canonical_environment template_canonical_environment (CEvar 0) (CEvar 0)
    (k .: eta) (k .: eta') k x y Hx eq_refl eq_refl HX HY).
  - intros i a b HA HB. change (a=eta i) in HA. change (b=eta' i) in HB.
    subst a b. apply HE.
  - exact (proj2 (template_evaluation_canonical M phi eta k v) HV).
  - exact (proj2 (template_evaluation_canonical M phi eta' k w) HW).
Qed.

Lemma quotation_atom_interval_substitution M equality a b a' b' t k x y v w source :
  x<>zeroM M -> t<>x ->
  quotation_allocation_avoids M source k x -> quotation_allocation_avoids M source k y ->
  named_replace M x y a a' -> named_replace M x y b b' ->
  quotation_atom M equality a b t k v -> quotation_atom M equality a' b' t k w ->
  named_substitution M v x y w.
Proof.
  intros Hx HT HX HY HA HB HV HW.
  assert (Halloc : forall z,quotation_allocation_avoids M source k z ->
    template_allocations_avoid M
      (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2) k z).
  { intros z HZ. apply template_allocations_avoid_offsets. intros i Hi. apply HZ.
    apply allocation_cap_extend. apply sf_numeral_lt.
    pose proof (quotation_atom_allocation_span equality). lia. }
  apply (template_evaluation_substitution M
    (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2)
    (quotation_atom_values a b t) (quotation_atom_values a' b' t) k x y v w Hx
    (Halloc x HX) (Halloc y HY)).
  - intros [|[|i]];[right;auto|exact HA|exact HB].
  - exact (proj1 (quotation_atom_evaluation M equality a b t k v) HV).
  - exact (proj1 (quotation_atom_evaluation M equality a' b' t k w) HW).
Qed.

Definition quotation_interval_substitution_at M source :=
  forall b c n d e m k t x y v w,
    x<>zeroM M -> t<>x ->
    quotation_allocation_avoids M source k x -> quotation_allocation_avoids M source k y ->
    environment_named_replace M b c n d e m x y ->
    numerical_quotation M source b c n k t v -> numerical_quotation M source d e m k t w ->
    named_substitution M v x y w.
Definition quotation_interval_substitution_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀ (¬ ($3 == zero) → ¬ ($4 == $3) →
    quotation_allocation_avoids_formula $12 $5 $3 →
    quotation_allocation_avoids_formula $12 $5 $2 →
    environment_named_replace_formula $11 $10 $9 $8 $7 $6 $3 $2 →
    numerical_quotation_formula $12 $11 $10 $9 $5 $4 $1 →
    numerical_quotation_formula $12 $8 $7 $6 $5 $4 $0 → named_substitution_formula $1 $3 $2 $0).
Local Opaque holds quotation_allocation_avoids_formula environment_named_replace_formula
  numerical_quotation_formula named_substitution_formula.
Lemma quotation_interval_substitution_definable M :
  Definable1 M (quotation_interval_substitution_at M).
Proof.
  exists quotation_interval_substitution_formula,(fun _=>zeroM M). intro source.
  unfold quotation_interval_substitution_formula,quotation_interval_substitution_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite quotation_allocation_avoids_correct.
  setoid_rewrite environment_named_replace_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite fresh_holds_eq. setoid_rewrite quotation_holds_false. reflexivity.
Qed.

Lemma quotation_interval_substitution_atom M equality a q source :
  sf_relation M (quotation_source_atom equality) a q source ->
  quotation_interval_substitution_at M source.
Proof.
  intros HS b c n d e m k t x y v w Hx HT HX HY HE HV HW.
  destruct (numerical_quotation_atom_inv M equality a q source b c n k t v HS HV)
    as [u [z [HU [HZ Hout]]]].
  destruct (numerical_quotation_atom_inv M equality a q source d e m k t w HS HW)
    as [u' [z' [HU' [HZ' Hout']]]].
  exact (quotation_atom_interval_substitution M equality u z u' z' t k x y v w source
    Hx HT HX HY (HE a u u' HU HU') (HE q z z' HZ HZ') Hout Hout').
Qed.

Lemma quotation_interval_substitution_binary M h a q source :
  sf_binary h -> sf_relation M h a q source ->
  quotation_interval_substitution_at M a -> quotation_interval_substitution_at M q ->
  quotation_interval_substitution_at M source.
Proof.
  intros Hh HS IHa IHq b c n d e m k t x y v w Hx HT HX HY HE HV HW.
  destruct (sf_relation_descent M h a q source HS) as [Ha Hq].
  assert (Hqlt : coding_lt M q source).
  { destruct Hh as [HH|[HH|HH]];subst h;exact Hq. }
  destruct (numerical_quotation_binary_inv M h a q source b c n k t v Hh HS HV)
    as [u [z [HU [HZ Hout]]]].
  destruct (numerical_quotation_binary_inv M h a q source d e m k t w Hh HS HW)
    as [u' [z' [HU' [HZ' Hout']]]].
  apply (quotation_binary_named_substitution M h u z u' z' v w x y Hx);try assumption.
  - exact (IHa b c n d e m k t x y u u' Hx HT
      (quotation_allocation_subformula M a source k x Ha HX)
      (quotation_allocation_subformula M a source k y Ha HY) HE HU HU').
  - exact (IHq b c n d e m k t x y z z' Hx HT
      (quotation_allocation_subformula M q source k x Hqlt HX)
      (quotation_allocation_subformula M q source k y Hqlt HY) HE HZ HZ').
Qed.

Lemma quotation_interval_substitution_unary M universal a source :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) source ->
  quotation_interval_substitution_at M a -> quotation_interval_substitution_at M source.
Proof.
  intros HS IH b c n d e m k t x y v w Hx HT HX HY HE HV HW.
  pose proof (proj1 (sf_relation_descent M (quotation_source_quantifier universal)
    a (zeroM M) source HS)) as Ha.
  pose proof (quotation_allocation_head M source k x HX) as HKx.
  pose proof (quotation_allocation_head M source k y HY) as HKy.
  destruct (numerical_quotation_unary_inv M universal a source b c n k t v HS HV)
    as [b' [c' [n' [u [HC [HU Hout]]]]]].
  destruct (numerical_quotation_unary_inv M universal a source d e m k t w HS HW)
    as [d' [e' [m' [u' [HD [HU' Hout']]]]]].
  apply (quotation_quantifier_named_substitution M universal k t u u' v w x y Hx HT HKx HKy);try assumption.
  exact (IH b' c' n' d' e' m' (succM M k) t x y u u' Hx HT
    (quotation_allocation_child M a source k x Ha HX)
    (quotation_allocation_child M a source k y Ha HY)
    (environment_named_replace_cons M b c n d e m b' c' n' d' e' m' x y k HE HKx HC HD)
    HU HU').
Qed.

Theorem numerical_quotation_interval_substitution M source : quotation_interval_substitution_at M source.
Proof.
  revert source. apply (sf_code_induction M (quotation_interval_substitution_at M)).
  - apply quotation_interval_substitution_definable.
  - intros b c n d e m k t x y v w Hx HT HX HY HE HV HW.
    rewrite (numerical_quotation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) HV),
      (numerical_quotation_invalid M (zeroM M) d e m k t w (or_introl eq_refl) HW).
    now apply named_substitution_one_fixed.
  - intros source Hbad b c n d e m k t x y v w Hx HT HX HY HE HV HW.
    rewrite (numerical_quotation_invalid M source b c n k t v (or_intror Hbad) HV),
      (numerical_quotation_invalid M source d e m k t w (or_intror Hbad) HW).
    now apply named_substitution_one_fixed.
  - intros a q source HS. exact (quotation_interval_substitution_atom M false a q source HS).
  - intros a q source HS. exact (quotation_interval_substitution_atom M true a q source HS).
  - exact (quotation_interval_substitution_binary M).
  - intros h a source Hh HS IH. destruct Hh as [HH|HH];subst h.
    + exact (quotation_interval_substitution_unary M true a source HS IH).
    + exact (quotation_interval_substitution_unary M false a source HS IH).
Qed.

Print Assumptions numerical_quotation_interval_substitution.
