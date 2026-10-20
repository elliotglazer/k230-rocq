(** Proof-producing fresh-base conversion for arbitrary internal source
    formulas. The induction predicate is an explicit PA formula. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  CodeDescent CodeTags NumericalProofs NumericalEquivalence NumericalEnvironments
  SetFormulaCodes SetCodeDescent QuotationPayloads QuotationRules NumericalQuotation
  QuotationFunctionality QuotationHygiene QuotationBinderFresh QuotationFormulaFresh
  QuotationNamedSubstitution QuotationAllocationBounds QuotationAllocationSubstitution
  QuotationRebaseHygiene QuotationGuardedAlpha QuotationAtomRebase
  FiniteTemplateEvaluation FiniteTemplateRebase TemplateNamedExclusions TemplateBinderRange
  QuotientAtomTemplates FreshNames.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma quotation_atom_interval_rebase M equality x z t k l v w source :
  quotation_allocation_avoids M source k (zeroM M) ->
  quotation_allocation_avoids M source k x -> quotation_allocation_avoids M source k z ->
  quotation_allocation_avoids M source k t ->
  quotation_allocation_avoids M source l (zeroM M) ->
  quotation_allocation_avoids M source l x -> quotation_allocation_avoids M source l z ->
  quotation_allocation_avoids M source l t ->
  quotation_atom M equality x z t k v -> quotation_atom M equality x z t l w ->
  numerical_equivalent M v w.
Proof.
  intros HK0 HKx HKz HKt HL0 HLx HLz HLt HV HW.
  assert (HA : forall fresh name,quotation_allocation_avoids M source fresh name ->
    template_allocations_avoid M
      (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2) fresh name).
  { intros fresh name H. apply template_allocations_avoid_offsets. intros i Hi.
    apply H. apply allocation_cap_extend. apply sf_numeral_lt.
    pose proof (quotation_atom_allocation_span equality). lia. }
  apply (finite_template_rebase M
    (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2)
    (quotation_atom_values x z t) k l v w).
  - split;[exact (HA k _ HK0)|]. intros [|[|i]];apply HA;assumption.
  - split;[exact (HA l _ HL0)|]. intros [|[|i]];apply HA;assumption.
  - exact (proj1 (quotation_atom_evaluation M equality x z t k v) HV).
  - exact (proj1 (quotation_atom_evaluation M equality x z t l w) HW).
Qed.

Lemma quotation_outer_alpha_interval M source a b c n k t y d e m d' e' m' u v f g universal :
  quotation_rebase_hygiene M source b c n k t ->
  environment_cons M b c n k d e m -> environment_cons M b c n y d' e' m' ->
  quotation_allocation_avoids M a (succM M k) y ->
  coding_lt M u y -> coding_lt M k y -> coding_lt M t y ->
  numerical_quotation M a d e m (succM M k) t u ->
  numerical_quotation M a d' e' m' (succM M k) t v ->
  quotation_quantifier M universal k t u f -> quotation_quantifier M universal y t v g ->
  numerical_equivalent M f g.
Proof.
  intros HH HC HC' HY Huy Hky Hty HU HV HF HG.
  assert (HK0 : k<>zeroM M) by exact (quotation_allocation_head M source k (zeroM M) (proj1 HH)).
  assert (HTk : t<>k).
  { intro E. apply (quotation_allocation_head M source k t (proj1 (proj2 HH))). symmetry. exact E. }
  assert (HkY : k<>y) by exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) k y Hky).
  assert (HTy : t<>y) by exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) t y Hty).
  assert (HY0 : y<>zeroM M).
  { intro E. subst y. exact (coding_not_lt_zero M u Huy). }
  apply (quotation_guarded_alpha M universal t k y u v f g HK0 HY0 HkY HTk HTy).
  - exact (numerical_quotation_matrix_binder_absent M a d e m k t u HU).
  - exact (formula_above_is_fresh M u y Huy).
  - apply (numerical_quotation_interval_substitution M a d e m d' e' m'
      (succM M k) t k y u v HK0 HTk).
    + apply quotation_allocation_below,coding_lt_succ.
    + exact HY.
    + exact (rebase_environment_head_replace M source b c n k t d e m y d' e' m' HH HC HC').
    + exact HU.
    + exact HV.
  - exact HF.
  - exact HG.
Qed.

Definition quotation_rebase_at M source :=
  forall b c n k l t v w,
    quotation_rebase_hygiene M source b c n k t -> quotation_rebase_hygiene M source b c n l t ->
    numerical_quotation M source b c n k t v -> numerical_quotation M source b c n l t w ->
    numerical_equivalent M v w.
Definition quotation_rebase_formula : form :=
  ∀∀∀∀∀∀∀∀ (quotation_rebase_hygiene_formula $8 $7 $6 $5 $4 $2 →
    quotation_rebase_hygiene_formula $8 $7 $6 $5 $3 $2 →
    numerical_quotation_formula $8 $7 $6 $5 $4 $2 $1 →
    numerical_quotation_formula $8 $7 $6 $5 $3 $2 $0 → numerical_equivalent_formula $1 $0).
Local Opaque holds quotation_rebase_hygiene_formula numerical_quotation_formula numerical_equivalent_formula.
Lemma quotation_rebase_definable M : Definable1 M (quotation_rebase_at M).
Proof.
  exists quotation_rebase_formula,(fun _=>zeroM M). intro source.
  unfold quotation_rebase_formula,quotation_rebase_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite quotation_rebase_hygiene_correct. setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite numerical_equivalent_formula_correct. reflexivity.
Qed.

Lemma quotation_rebase_invalid M source :
  (source=zeroM M \/ sf_invalid M source) -> quotation_rebase_at M source.
Proof.
  intros Hbad b c n k l t v w HK HL HV HW.
  rewrite (numerical_quotation_invalid M source b c n k t v Hbad HV),
    (numerical_quotation_invalid M source b c n l t w Hbad HW).
  apply numerical_equivalent_refl.
Qed.

Lemma quotation_rebase_atom M equality a q source :
  sf_relation M (quotation_source_atom equality) a q source -> quotation_rebase_at M source.
Proof.
  intros HS b c n k l t v w [HK0 [HKt HKE]] [HL0 [HLt HLE]] HV HW.
  destruct (numerical_quotation_atom_inv M equality a q source b c n k t v HS HV)
    as [x [z [HX [HZ Hout]]]].
  destruct (numerical_quotation_atom_inv M equality a q source b c n l t w HS HW)
    as [x' [z' [HX' [HZ' Hout']]]].
  assert (x'=x) by exact (environment_lookup_functional M b c n a x' x HX' HX).
  assert (z'=z) by exact (environment_lookup_functional M b c n q z' z HZ' HZ).
  subst x' z'. exact (quotation_atom_interval_rebase M equality x z t k l v w source
    HK0 (HKE a x HX) (HKE q z HZ) HKt HL0 (HLE a x HX) (HLE q z HZ) HLt Hout Hout').
Qed.

Lemma quotation_rebase_binary M h a q source :
  sf_binary h -> sf_relation M h a q source ->
  quotation_rebase_at M a -> quotation_rebase_at M q -> quotation_rebase_at M source.
Proof.
  intros Hh HS IHa IHq b c n k l t v w HK HL HV HW.
  destruct (sf_relation_descent M h a q source HS) as [Ha Hq].
  assert (Hqlt : coding_lt M q source).
  { destruct Hh as [HH|[HH|HH]];subst h;exact Hq. }
  destruct (numerical_quotation_binary_inv M h a q source b c n k t v Hh HS HV)
    as [x [z [HX [HZ Hout]]]].
  destruct (numerical_quotation_binary_inv M h a q source b c n l t w Hh HS HW)
    as [x' [z' [HX' [HZ' Hout']]]].
  apply (numerical_equivalent_binary M h x z x' z' v w);try assumption.
  - exact (IHa b c n k l t x x'
      (quotation_rebase_hygiene_subformula M a source b c n k t Ha HK)
      (quotation_rebase_hygiene_subformula M a source b c n l t Ha HL) HX HX').
  - exact (IHq b c n k l t z z'
      (quotation_rebase_hygiene_subformula M q source b c n k t Hqlt HK)
      (quotation_rebase_hygiene_subformula M q source b c n l t Hqlt HL) HZ HZ').
Qed.

Lemma quotation_rebase_unary M universal a source :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) source ->
  quotation_rebase_at M a -> quotation_rebase_at M source.
Proof.
  intros HS IH b c n k l t v w HK HL HV HW.
  pose proof (proj1 (sf_relation_descent M (quotation_source_quantifier universal)
    a (zeroM M) source HS)) as Ha.
  destruct (numerical_quotation_unary_inv M universal a source b c n k t v HS HV)
    as [d [e [m [x [HC [HX Hout]]]]]].
  destruct (numerical_quotation_unary_inv M universal a source b c n l t w HS HW)
    as [d' [e' [m' [z [HC' [HZ Hout']]]]]].
  destruct (quotation_common_fresh M a (succM M k) (succM M l) x z t)
    as [y [Hxy [Hzy [Hty [Hky [Hly [HYk HYl]]]]]]].
  destruct (environment_cons_total M b c n y) as [yb [yc [yn HYC]]].
  destruct (numerical_quotation_total M a yb yc yn (succM M k) t) as [u HU].
  destruct (numerical_quotation_total M a yb yc yn (succM M l) t) as [u' HU'].
  destruct (quotation_quantifier_total M universal y t u) as [f HF].
  destruct (quotation_quantifier_total M universal y t u') as [g HG].
  apply (numerical_equivalent_trans M v f w).
  - apply (quotation_outer_alpha_interval M source a b c n k t y d e m yb yc yn x u v f universal
      HK HC HYC HYk Hxy);try assumption.
    exact (coding_lt_trans M k (succM M k) y (coding_lt_succ M k) Hky).
  - apply (numerical_equivalent_trans M f g w).
    + apply (quotation_guarded_equivalent M universal y t u u' f g);try assumption.
      exact (IH yb yc yn (succM M k) (succM M l) t u u'
        (quotation_rebase_hygiene_child M a source b c n k t y yb yc yn Ha HK HYk HYC)
        (quotation_rebase_hygiene_child M a source b c n l t y yb yc yn Ha HL HYl HYC) HU HU').
    + apply numerical_equivalent_sym.
      apply (quotation_outer_alpha_interval M source a b c n l t y d' e' m' yb yc yn z u' w g universal
        HL HC' HYC HYl Hzy);try assumption.
      exact (coding_lt_trans M l (succM M l) y (coding_lt_succ M l) Hly).
Qed.

Theorem numerical_quotation_rebase M source : quotation_rebase_at M source.
Proof.
  revert source. apply (sf_code_induction M (quotation_rebase_at M)).
  - apply quotation_rebase_definable.
  - apply quotation_rebase_invalid. now left.
  - intros source Hbad. apply quotation_rebase_invalid. now right.
  - intros a q source HS. exact (quotation_rebase_atom M false a q source HS).
  - intros a q source HS. exact (quotation_rebase_atom M true a q source HS).
  - exact (quotation_rebase_binary M).
  - intros h a source Hh HS IH. destruct Hh as [HH|HH];subst h.
    + exact (quotation_rebase_unary M true a source HS IH).
    + exact (quotation_rebase_unary M false a source HS IH).
Qed.

Corollary numerical_quotation_rebase_safe M source b c n k l t v w :
  quotation_safe M b c n k t -> quotation_safe M b c n l t ->
  numerical_quotation M source b c n k t v -> numerical_quotation M source b c n l t w ->
  numerical_equivalent M v w.
Proof.
  intros HK HL HV HW. exact (numerical_quotation_rebase M source b c n k l t v w
    (quotation_safe_rebase_hygiene M source b c n k t HK)
    (quotation_safe_rebase_hygiene M source b c n l t HL) HV HW).
Qed.

Print Assumptions quotation_rebase_definable.
Print Assumptions numerical_quotation_rebase.
Print Assumptions numerical_quotation_rebase_safe.
