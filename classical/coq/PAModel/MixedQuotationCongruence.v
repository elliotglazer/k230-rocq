(** Uniform mixed quotient congruence for internally coded source formulas.
    This theorem is CONDITIONAL on the explicit uniform atom-equivalence
    package below. It does not establish that package from the K axioms. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions CodeDescent CodeTags NumericalProofs NumericalContexts
  NumericalEnvironments NumericalQuotation QuotationFunctionality QuotationRules
  QuotationPayloads QuotationHygiene QuotationRebase SourceBounded SetFormulaCodes
  SetCodeDescent ContextualProofs ContextualEquivalence ContextualQuotationCongruence
  ContextualPropositional ProofTemplates TemplateCD TemplatePropositional
  NumericalEquivalence StableContextSupport SupportedQuotientEnvironments
  SupportedEigenvariables SubstitutionEnvironmentTotal.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma mixed_contextual_implication_trans M cb cc cn a b c :
  contextual_implies M cb cc cn a b -> contextual_implies M cb cc cn b c ->
  contextual_implies M cb cc cn a c.
Proof.
  intros HAB HBC. set (rho:=a .: b .: c .: fun _=>zeroM M).
  apply (proj1 (contextual_implies_expression M cb cc cn rho
    (CEvar 0) (CEvar 2) a c eq_refl eq_refl)).
  apply (contextual_expression_derivation M cb cc cn rho
    (E_wim (CEvar 0) (CEvar 1) :: E_wim (CEvar 1) (CEvar 2) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (proj2 (contextual_implies_expression M cb cc cn rho
        (CEvar 0) (CEvar 1) a b eq_refl eq_refl) HAB).
    + exact (proj2 (contextual_implies_expression M cb cc cn rho
        (CEvar 1) (CEvar 2) b c eq_refl eq_refl) HBC).
  - apply template_deduction.
    eapply dmp with (a:=CEvar 1);[apply dhyp;cbn;tauto|].
    eapply dmp with (a:=CEvar 0);apply dhyp;cbn;tauto.
Qed.
Lemma mixed_contextual_equivalence_trans M cb cc cn a b c :
  contextual_equivalence M cb cc cn a b -> contextual_equivalence M cb cc cn b c ->
  contextual_equivalence M cb cc cn a c.
Proof.
  intros [HAB HBA] [HBC HCB]. split;eapply mixed_contextual_implication_trans;eassumption.
Qed.
Lemma mixed_contextual_equivalence_sym M cb cc cn a b :
  contextual_equivalence M cb cc cn a b -> contextual_equivalence M cb cc cn b a.
Proof. intros [HAB HBA]. now split. Qed.

(** The only unproved interface in the final conditional theorem. It is
    uniform in atom kind, name values, and the two hygienic allocation bases.
    Establishing it requires the KLogic quotient atom certificates. *)
Definition uniform_mixed_atom_equivalence M t cb cc cn :=
  forall equality k l x y x' y' f g,
    quotient_pair_safe M t x y k -> quotient_pair_safe M t x' y' l ->
    supported_quotient_pair M cb cc cn t x x' ->
    supported_quotient_pair M cb cc cn t y y' ->
    quotation_atom M equality x y t k f -> quotation_atom M equality x' y' t l g ->
    contextual_equivalence M cb cc cn f g.

Definition mixed_quotation_property M t cb cc cn source :=
  forall bound b c n d e m k l f g,
    source_bounded M source bound ->
    quotation_safe M b c n k t -> quotation_safe M d e m l t ->
    supported_quotient_environments M b c n d e m bound t cb cc cn ->
    numerical_quotation M source b c n k t f -> numerical_quotation M source d e m l t g ->
    contextual_equivalence M cb cc cn f g.

Definition mixed_quotation_property_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀ (
    source_bounded_accept_formula $11 $10 →
    quotation_safe_formula $9 $8 $7 $3 $12 →
    quotation_safe_formula $6 $5 $4 $2 $12 →
    supported_quotient_environments_formula $9 $8 $7 $6 $5 $4 $10 $12 $13 $14 $15 →
    numerical_quotation_formula $11 $9 $8 $7 $3 $12 $1 →
    numerical_quotation_formula $11 $6 $5 $4 $2 $12 $0 →
    contextual_equivalence_formula $13 $14 $15 $1 $0).
Local Opaque holds source_bounded_accept_formula quotation_safe_formula
  supported_quotient_environments_formula numerical_quotation_formula contextual_equivalence_formula.
Lemma mixed_quotation_property_definable M t cb cc cn :
  Definable1 M (mixed_quotation_property M t cb cc cn).
Proof.
  exists mixed_quotation_property_formula,(t .: cb .: cc .: cn .: fun _=>zeroM M).
  intro source. unfold mixed_quotation_property_formula,mixed_quotation_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite quotation_safe_formula_correct.
  setoid_rewrite supported_quotient_environments_correct.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite contextual_equivalence_formula_correct. reflexivity.
Qed.

Lemma mixed_quotation_invalid M t cb cc cn source :
  (source=zeroM M \/ sf_invalid M source) -> mixed_quotation_property M t cb cc cn source.
Proof.
  intros Hbad bound b c n d e m k l f g HB HK HL HE HF HG.
  rewrite (numerical_quotation_invalid M source b c n k t f Hbad HF),
    (numerical_quotation_invalid M source d e m l t g Hbad HG).
  apply contextual_equivalence_global,numerical_equivalent_refl.
Qed.

Lemma mixed_quotation_atom M t cb cc cn equality a z source :
  uniform_mixed_atom_equivalence M t cb cc cn ->
  sf_relation M (quotation_source_atom equality) a z source ->
  mixed_quotation_property M t cb cc cn source.
Proof.
  intros HAtoms HS bound b c n d e m k l f g HB HK HL HE HF HG.
  assert (HA : sb_atomic (quotation_source_atom equality)).
  { destruct equality;[right|left];reflexivity. }
  destruct (proj1 (source_bounded_accept_atom M (quotation_source_atom equality)
    a z source bound HA HS) HB) as [HAbound HZbound].
  destruct (numerical_quotation_atom_inv M equality a z source b c n k t f HS HF)
    as [x [y [HX [HY Hout]]]].
  destruct (numerical_quotation_atom_inv M equality a z source d e m l t g HS HG)
    as [x' [y' [HX' [HY' Hout']]]].
  apply (HAtoms equality k l x y x' y' f g);try assumption.
  - destruct HK as [Ht Henv]. split;[exact (environment_below_zero M b c n k Henv)|].
    split;[exact Ht|]. split;[exact (Henv a x HX)|exact (Henv z y HY)].
  - destruct HL as [Ht Henv]. split;[exact (environment_below_zero M d e m l Henv)|].
    split;[exact Ht|]. split;[exact (Henv a x' HX')|exact (Henv z y' HY')].
  - exact (HE a x x' HAbound HX HX').
  - exact (HE z y y' HZbound HY HY').
Qed.

Lemma mixed_quotation_binary M t cb cc cn h a z source :
  sf_binary h -> sf_relation M h a z source ->
  mixed_quotation_property M t cb cc cn a -> mixed_quotation_property M t cb cc cn z ->
  mixed_quotation_property M t cb cc cn source.
Proof.
  intros Hh HS IHa IHz bound b c n d e m k l f g HB HK HL HE HF HG.
  destruct (proj1 (source_bounded_accept_binary M h a z source bound Hh HS) HB) as [HBa HBz].
  destruct (numerical_quotation_binary_inv M h a z source b c n k t f Hh HS HF)
    as [x [y [HX [HY Hout]]]].
  destruct (numerical_quotation_binary_inv M h a z source d e m l t g Hh HS HG)
    as [x' [y' [HX' [HY' Hout']]]].
  apply (contextual_equivalence_binary M cb cc cn h x y x' y' f g);try assumption.
  - exact (IHa bound b c n d e m k l x x' HBa HK HL HE HX HX').
  - exact (IHz bound b c n d e m k l y y' HBz HK HL HE HY HY').
Qed.

Lemma mixed_quotation_unary M t cb cc cn universal a source :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) source ->
  mixed_quotation_property M t cb cc cn a -> mixed_quotation_property M t cb cc cn source.
Proof.
  intros HS IH bound b c n d e m k l f g HB HK HL HE HF HG.
  assert (Hhead : sf_unary (quotation_source_quantifier universal)).
  { destruct universal;[left|right];reflexivity. }
  pose proof (proj1 (source_bounded_accept_unary M (quotation_source_quantifier universal)
    a source bound Hhead HS) HB) as HBa.
  destruct (supported_eigenname_total M b c n k t cb cc cn l HK)
    as [fresh [HKfresh [Hkfresh [Hctxfresh Hlfresh]]]].
  pose proof (quotation_safe_above M d e m l fresh t HL Hlfresh) as HLfresh.
  destruct (numerical_quotation_total M source b c n fresh t) as [f' HF'].
  destruct (numerical_quotation_total M source d e m fresh t) as [g' HG'].
  pose proof (numerical_quotation_rebase_safe M source b c n k fresh t f f'
    HK HKfresh HF HF') as EQf.
  pose proof (numerical_quotation_rebase_safe M source d e m l fresh t g g'
    HL HLfresh HG HG') as EQg.
  destruct (numerical_quotation_unary_inv M universal a source b c n fresh t f' HS HF')
    as [b' [c' [n' [x [HC [HX Hout]]]]]].
  destruct (numerical_quotation_unary_inv M universal a source d e m fresh t g' HS HG')
    as [d' [e' [m' [y [HD [HY Hout']]]]]].
  assert (HchildEq : contextual_equivalence M cb cc cn x y).
  { apply (IH (succM M bound) b' c' n' d' e' m' (succM M fresh) (succM M fresh) x y HBa).
    - exact (quotation_safe_cons M b c n fresh t b' c' n' HKfresh HC).
    - exact (quotation_safe_cons M d e m fresh t d' e' m' HLfresh HD).
    - exact (supported_quotient_environments_cons M b c n d e m bound t cb cc cn
        fresh b' c' n' d' e' m' HE HC HD).
    - exact HX.
    - exact HY. }
  apply (mixed_contextual_equivalence_trans M cb cc cn f f' g).
  - now apply contextual_equivalence_global.
  - apply (mixed_contextual_equivalence_trans M cb cc cn f' g' g).
    + exact (contextual_equivalence_guarded M cb cc cn universal fresh t x y f' g'
        Hctxfresh HchildEq Hout Hout').
    + apply contextual_equivalence_global,numerical_equivalent_sym,EQg.
Qed.

Theorem numerical_mixed_quotation_congruence M t cb cc cn :
  uniform_mixed_atom_equivalence M t cb cc cn ->
  forall source,mixed_quotation_property M t cb cc cn source.
Proof.
  intro HAtoms. apply (sf_code_induction M (mixed_quotation_property M t cb cc cn)).
  - apply mixed_quotation_property_definable.
  - apply mixed_quotation_invalid. now left.
  - intros source Hbad. apply mixed_quotation_invalid. now right.
  - intros a z source HS. exact (mixed_quotation_atom M t cb cc cn false a z source HAtoms HS).
  - intros a z source HS. exact (mixed_quotation_atom M t cb cc cn true a z source HAtoms HS).
  - exact (mixed_quotation_binary M t cb cc cn).
  - intros h a source Hh HS IH. destruct Hh as [Hh|Hh];subst h.
    + exact (mixed_quotation_unary M t cb cc cn true a source HS IH).
    + exact (mixed_quotation_unary M t cb cc cn false a source HS IH).
Qed.

Print Assumptions mixed_contextual_equivalence_trans.
Print Assumptions mixed_quotation_property_definable.
Print Assumptions mixed_quotation_unary.
Print Assumptions numerical_mixed_quotation_congruence.
