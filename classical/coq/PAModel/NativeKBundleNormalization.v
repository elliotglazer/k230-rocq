(** Normalize the fixed regular named skeleton, without recursively
    replacing or analyzing its arbitrary internally coded matrix holes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent NumericalProofs ProofTemplates
  SetFormulaCodes SetCodeDescent SourceBounded SourceRenamingBounds NumericalRenaming
  NumericalEquality RawEqualityRows RawEqualityCalibration RawBinderRenaming
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawSourcePropositional RawLogicalRow1
  RawSourceConjunction RawSourceExistential SourceZFCPrograms
  SourceZFCQuantifierCongruence NativeKBundle NativeNamedRegularity.
From Stdlib Require Import Bool.Bool.
Unset Implicit Arguments.

Theorem native_named_normalization M env t :native_named_regular t=true ->
  forall raw source native,code_relation M env (native_named_raw_expression t) raw ->
    raw_source_image M raw source ->native_named_evaluation M env t native ->
    source_zfc_equivalent M source native.
Proof.
  induction t as [i|eq a b|a IHa b IHb|a IHa b IHb|x a IH|x a IH];
    intros HRegular raw source native HRaw HSource HNative;
    cbn [native_named_regular native_named_raw_expression native_named_evaluation] in
      HRegular,HRaw,HNative.
  - change (raw=env i) in HRaw. subst raw.
    rewrite <- (raw_source_image_functional M (env i) source native HSource HNative).
    destruct (raw_source_image_bounded M (env i) source HSource) as (k&HK).
    exact (source_zfc_equivalent_refl M source k HK).
  - destruct HNative as (u&v&HU&HV&HN).
    assert (HS:sf_relation M (if eq then SFEqual else SFMember) u v source).
    { destruct eq.
      - exact (raw_source_equal_inv M u v raw source
          (proj1 (expression_equality_graph M env a b u v raw HU HV) HRaw) HSource).
      - exact (raw_source_member_inv M u v raw source
          (expression_membership_graph M env a b u v raw HU HV HRaw) HSource). }
    rewrite <- (sf_relation_functional M (if eq then SFEqual else SFMember) u v source native HS HN).
    destruct (raw_source_image_bounded M raw source HSource) as (k&HK).
    exact (source_zfc_equivalent_refl M source k HK).
  - apply andb_true_iff in HRegular. destruct HRegular as [HRegs HP].
    apply andb_true_iff in HRegs. destruct HRegs as [HRA HRB].
    destruct HNative as (na&nb&HNA&HNB&HNI).
    destruct (code_relation_total M (native_named_raw_expression a) env) as (ra&HRAE).
    destruct (code_relation_total M (native_named_raw_expression b) env) as (rb&HRBE).
    pose proof (expression_implication_graph M env _ _ ra rb raw HRAE HRBE HRaw) as HImpl.
    pose proof (raw_implication_nonzero_consequent M ra rb raw
      (native_named_positive_nonzero M env b HP rb HRBE) HImpl) as HRawNZ.
    destruct (raw_source_implication_inv M ra rb raw source HRawNZ HImpl HSource)
      as (sa&sb&HSA&HSB&HSImpl).
    exact (source_zfc_equivalent_binary_finite M SFImpl sa sb na nb source native (or_introl eq_refl)
      (raw_source_image_bounded M ra sa HSA) (raw_source_image_bounded M rb sb HSB)
      (native_named_evaluation_bounded M env a na HNA) (native_named_evaluation_bounded M env b nb HNB)
      (IHa HRA ra sa na HRAE HSA HNA) (IHb HRB rb sb nb HRBE HSB HNB) HSImpl HNI).
  - apply andb_true_iff in HRegular. destruct HRegular as [HRA HRB].
    destruct HNative as (na&nb&HNA&HNB&HNI).
    destruct (code_relation_total M (native_named_raw_expression a) env) as (ra&HRAE).
    destruct (code_relation_total M (native_named_raw_expression b) env) as (rb&HRBE).
    destruct (code_relation_total M (E_wn (native_named_raw_expression b)) env) as (neg&HN).
    destruct (code_relation_total M (E_wim (native_named_raw_expression a)
      (E_wn (native_named_raw_expression b))) env) as (inner&HI).
    pose proof (expression_implication_graph M env _ (CEconst 1) rb (code_numeral M 1) neg HRBE eq_refl HN) as HNeg.
    pose proof (expression_implication_graph M env _ _ ra neg inner HRAE HN HI) as HInner.
    pose proof (expression_implication_graph M env _ (CEconst 1) inner (code_numeral M 1) raw HI eq_refl HRaw) as HEnc.
    destruct (raw_source_image_total M ra) as (sa&HSA),(raw_source_image_total M rb) as (sb&HSB).
    destruct (sf_relation_total M SFAnd sa sb) as (mid&HMid).
    destruct (sf_relation_total M SFImpl source mid) as (forward&HF).
    destruct (sf_relation_total M SFImpl mid source) as (reverse&HR).
    destruct (raw_conjunction_source_normalization M ra rb neg inner raw sa sb source mid forward reverse
      HNeg HInner HEnc HSA HSB HSource HMid HF HR) as [PF PR].
    assert (HMidBound:exists k,source_bounded M mid k).
    { exact (source_binary_bound_exists M SFAnd sa sb mid ltac:(unfold sf_binary;auto) HMid
        (raw_source_image_bounded M ra sa HSA) (raw_source_image_bounded M rb sb HSB)). }
    apply (source_zfc_equivalent_trans_finite M source mid native
      (raw_source_image_bounded M raw source HSource) HMidBound
      (native_named_evaluation_bounded M env (NNTAnd a b) native
        ltac:(exists na,nb;auto))).
    + split;[exact (source_zfc_implies_from_proof M source mid forward HF PF)|
        exact (source_zfc_implies_from_proof M mid source reverse HR PR)].
    + exact (source_zfc_equivalent_binary_finite M SFAnd sa sb na nb mid native (or_intror eq_refl)
        (raw_source_image_bounded M ra sa HSA) (raw_source_image_bounded M rb sb HSB)
        (native_named_evaluation_bounded M env a na HNA) (native_named_evaluation_bounded M env b nb HNB)
        (IHa HRA ra sa na HRAE HSA HNA) (IHb HRB rb sb nb HRBE HSB HNB) HMid HNI).
  - destruct HNative as (name&body&nb&nc&closed&HN&HB&HMapN&HRN&HOutN).
    destruct (code_relation_total M (native_named_raw_expression a) env) as (ra&HRA).
    pose proof (expression_universal_graph M env x _ name ra raw HN HRA HRaw) as HAll.
    destruct (raw_source_universal_inv M name ra raw source HAll HSource)
      as (sa&rb&rc&sc&HSA&HMapR&HRR&HOutR).
    destruct (numerical_renaming_total M sa nb nc (succM M name) (succM M (zeroM M))) as (sn&HRS).
    assert (E:sc=sn).
    { exact (numerical_renaming_functional_equivalent M sa rb rc (succM M name) nb nc (succM M name)
        (succM M (zeroM M)) sc sn (raw_binder_renaming_equivalent M name rb rc nb nc HMapR HMapN) HRR HRS). }
    subst sc.
    assert (HSBound:exists k,source_bounded M sn k).
    { destruct (raw_source_image_bounded M ra sa HSA) as (k&HK). exists (succM M k).
      exact (numerical_renaming_preserves_bound M sa nb nc (succM M name) (succM M (zeroM M)) sn
        k (succM M k) HK HRS (raw_binder_maps_bound M name nb nc k HMapN)). }
    assert (HNBound:exists k,source_bounded M closed k).
    { destruct (native_named_evaluation_bounded M env a body HB) as (k&HK). exists (succM M k).
      exact (numerical_renaming_preserves_bound M body nb nc (succM M name) (succM M (zeroM M)) closed
        k (succM M k) HK HRN (raw_binder_maps_bound M name nb nc k HMapN)). }
    exact (source_zfc_equivalent_quantifier_finite M SFAll sn closed source native (or_introl eq_refl)
      HSBound HNBound (source_zfc_equivalent_renaming M sa body nb nc (succM M name)
        (succM M (zeroM M)) sn closed (IH HRegular ra sa body HRA HSA HB) HRS HRN) HOutR HOutN).
  - destruct HNative as (name&body&nb&nc&closed&HN&HB&HMapN&HRN&HOutN).
    destruct (code_relation_total M (native_named_raw_expression a) env) as (ra&HRA).
    destruct (code_relation_total M (E_wn (native_named_raw_expression a)) env) as (neg&HNeg).
    destruct (code_relation_total M (E_wal x (E_wn (native_named_raw_expression a))) env) as (all&HAll).
    pose proof (expression_implication_graph M env _ (CEconst 1) ra (code_numeral M 1) neg HRA eq_refl HNeg) as HNGraph.
    pose proof (expression_universal_graph M env x _ name neg all HN HNeg HAll) as HAGraph.
    pose proof (expression_implication_graph M env _ (CEconst 1) all (code_numeral M 1) raw HAll eq_refl HRaw) as HEGraph.
    destruct (raw_source_image_total M ra) as (sa&HSA).
    destruct (numerical_renaming_total M sa nb nc (succM M name) (succM M (zeroM M))) as (sn&HRS).
    destruct (sf_relation_total M SFEx sn (zeroM M)) as (mid&HMid).
    destruct (sf_relation_total M SFImpl source mid) as (forward&HF).
    destruct (sf_relation_total M SFImpl mid source) as (reverse&HR).
    destruct (raw_existential_source_normalization M name ra neg all raw sa source nb nc sn mid forward reverse
      HNGraph HAGraph HEGraph HSA HSource HMapN HRS HMid HF HR) as [PF PR].
    assert (HSBound:exists k,source_bounded M sn k).
    { destruct (raw_source_image_bounded M ra sa HSA) as (k&HK). exists (succM M k).
      exact (numerical_renaming_preserves_bound M sa nb nc (succM M name) (succM M (zeroM M)) sn
        k (succM M k) HK HRS (raw_binder_maps_bound M name nb nc k HMapN)). }
    assert (HNBound:exists k,source_bounded M closed k).
    { destruct (native_named_evaluation_bounded M env a body HB) as (k&HK). exists (succM M k).
      exact (numerical_renaming_preserves_bound M body nb nc (succM M name) (succM M (zeroM M)) closed
        k (succM M k) HK HRN (raw_binder_maps_bound M name nb nc k HMapN)). }
    assert (HMidBound:exists k,source_bounded M mid k).
    { destruct (raw_source_image_bounded M ra sa HSA) as (k&HK). exists k.
      apply (proj2 (source_bounded_accept_unary M SFEx sn mid k (or_intror eq_refl) HMid)).
      exact (numerical_renaming_preserves_bound M sa nb nc (succM M name) (succM M (zeroM M)) sn
        k (succM M k) HK HRS (raw_binder_maps_bound M name nb nc k HMapN)). }
    apply (source_zfc_equivalent_trans_finite M source mid native
      (raw_source_image_bounded M raw source HSource) HMidBound
      (native_named_evaluation_bounded M env (NNTEx x a) native
        ltac:(exists name,body,nb,nc,closed;repeat first [assumption|split]))).
    + split;[exact (source_zfc_implies_from_proof M source mid forward HF PF)|
        exact (source_zfc_implies_from_proof M mid source reverse HR PR)].
    + exact (source_zfc_equivalent_quantifier_finite M SFEx sn closed mid native (or_intror eq_refl)
        HSBound HNBound (source_zfc_equivalent_renaming M sa body nb nc (succM M name)
          (succM M (zeroM M)) sn closed (IH HRegular ra sa body HRA HSA HB) HRS HRN) HMid HOutN).
Qed.

Theorem native_K_bundle_normalization M env raw source native :
  code_relation M env code_bundle raw ->raw_source_image M raw source ->
  native_named_evaluation M env native_K_bundle_template native ->source_zfc_equivalent M source native.
Proof.
  intros HR HS HN. apply (native_named_normalization M env native_K_bundle_template native_K_bundle_regular
    raw source native);[exact HR|exact HS|exact HN].
Qed.

Print Assumptions native_named_normalization.
Print Assumptions native_K_bundle_normalization.
