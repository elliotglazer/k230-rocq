(** Closing an arbitrary internally finite prefix of restricted universal
    quantifiers. The premise proves the open matrix in every safe numerical
    environment. The proof uses PA induction on the internal prefix length. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeTags
  NumericalProofs NumericalSetClosure NumericalQuotation NumericalEnvironments
  QuotationHygiene QuotationRules QuotationFunctionality QuotationRebase
  QuotationPayloads ContextualProofs ContextualLogic ContextualGuardedQuantifiers
  SupportedEigenvariables QuotedSameBaseRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition prefix_quotation_provable M body t cb cc cn n :=
  forall f eb ec en fresh q,
    all_prefix M n body f -> quotation_safe M eb ec en fresh t ->
    numerical_quotation M f eb ec en fresh t q ->
    contextually_provable M cb cc cn q.

Definition prefix_quotation_formula : form :=
  ∀∀∀∀∀∀ (all_prefix_formula $6 $7 $5 →
    quotation_safe_formula $4 $3 $2 $1 $8 →
    numerical_quotation_formula $5 $4 $3 $2 $1 $8 $0 →
    contextually_provable_formula $9 $10 $11 $0).

Local Opaque holds all_prefix_formula quotation_safe_formula
  numerical_quotation_formula contextually_provable_formula.
Lemma prefix_quotation_provable_definable M body t cb cc cn :
  Definable1 M (prefix_quotation_provable M body t cb cc cn).
Proof.
  exists prefix_quotation_formula,(body .: t .: cb .: cc .: cn .: fun _=>zeroM M).
  intro n. unfold prefix_quotation_provable,prefix_quotation_formula.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite all_prefix_formula_correct.
  setoid_rewrite quotation_safe_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite contextually_provable_formula_correct. reflexivity.
Qed.

Theorem numerical_quotation_prefix_closure M body t cb cc cn :
  (forall eb ec en fresh q, quotation_safe M eb ec en fresh t ->
    numerical_quotation M body eb ec en fresh t q ->
    contextually_provable M cb cc cn q) ->
  forall n, prefix_quotation_provable M body t cb cc cn n.
Proof.
  intro HOpen. apply (definable_induction M
    (prefix_quotation_provable M body t cb cc cn)).
  - apply prefix_quotation_provable_definable.
  - intros f eb ec en fresh q HP HS HQ.
    apply all_prefix_zero_forward in HP. subst f. exact (HOpen eb ec en fresh q HS HQ).
  - intros n IH f eb ec en fresh q HP HS HQ.
    destruct (all_prefix_succ_forward M n body f HP) as [previous [HPrevious HAll]].
    destruct (supported_eigenname_total M eb ec en fresh t cb cc cn (zeroM M) HS)
      as [k [HK [Hfk [HContext HExtra]]]].
    destruct (numerical_quotation_total M f eb ec en k t) as [qk HQk].
    apply (contextual_equivalent_forward M cb cc cn qk q
      (numerical_quotation_rebase_safe M f eb ec en k fresh t qk q HK HS HQk HQ)).
    destruct (numerical_quotation_unary_inv M true previous f eb ec en k t qk HAll HQk)
      as [fb [fc [fn [matrix [HEnv [HMatrix HOutput]]]]]].
    pose proof (IH previous fb fc fn (succM M k) matrix HPrevious
      (quotation_safe_cons M eb ec en k t fb fc fn HK HEnv) HMatrix) as PMatrix.
    destruct (tagged_pair_total M 1 t k) as [dom HDom].
    destruct (contextual_implication_intro M cb cc cn dom matrix PMatrix)
      as [guard [HGuard PGuard]].
    apply (contextual_gen M cb cc cn k guard qk HContext PGuard).
    exact (proj1 (quotation_guarded_all_graph M k t matrix dom guard qk HDom HGuard) HOutput).
Qed.

Print Assumptions prefix_quotation_provable_definable.
Print Assumptions numerical_quotation_prefix_closure.
