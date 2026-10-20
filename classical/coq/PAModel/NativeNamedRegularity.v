From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  CodeDescent NumericalProofs ProofTemplates SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone
  RawSourceImageInversion RawSourcePropositional RawLogicalRow1 RawEqualityCalibration
  NumericalEquality RawEqualityRows NativeKBundle
  SourceZFCPrograms SourceZFCPropositionalCongruence SourceZFCQuantifierCongruence.
From Stdlib Require Import Bool.Bool.
Unset Implicit Arguments.

Theorem native_named_positive_nonzero M env t :native_named_positive t=true ->
  forall out,code_relation M env (native_named_raw_expression t) out ->out<>zeroM M.
Proof.
  induction t as [i|eq a b|a IHa b IHb|a IHa b IHb|x a IH|x a IH];intros HP out HO;
    cbn [native_named_positive native_named_raw_expression] in HP,HO.
  - discriminate HP.
  - destruct (code_relation_total M a env) as (u&HU),(code_relation_total M b env) as (v&HV).
    destruct eq.
    + exact (raw_positive_tag_nonzero M 3 u v out ltac:(discriminate)
        (proj1 (expression_equality_graph M env a b u v out HU HV) HO)).
    + exact (raw_positive_tag_nonzero M 1 u v out ltac:(discriminate)
        (expression_membership_graph M env a b u v out HU HV HO)).
  - destruct (code_relation_total M (native_named_raw_expression a) env) as (u&HU).
    destruct (code_relation_total M (native_named_raw_expression b) env) as (v&HV).
    pose proof (expression_implication_graph M env _ _ u v out HU HV HO) as HI.
    intro E. subst out. destruct (raw_zero_implication_arguments M u v HI) as [EU EV].
    apply orb_true_iff in HP. destruct HP as [HP|HP].
    + exact (IHa HP u HU EU).
    + exact (IHb HP v HV EV).
  - destruct (code_relation_total M
      (E_wim (native_named_raw_expression a) (E_wn (native_named_raw_expression b))) env) as (inner&HI).
    exact (raw_implication_nonzero_consequent M inner (code_numeral M 1) out
      (raw_positive_tag_nonzero M 1 (zeroM M) (zeroM M) (code_numeral M 1)
        ltac:(discriminate) (raw_one_membership_graph M))
      (expression_implication_graph M env _ (CEconst 1) inner (code_numeral M 1) out HI eq_refl HO)).
  - destruct (code_relation_total M x env) as (name&HN).
    destruct (code_relation_total M (native_named_raw_expression a) env) as (body&HB).
    apply (raw_positive_tag_nonzero M 2 name body out ltac:(discriminate)).
    apply universal_graph_tagged. exact (expression_universal_graph M env x _ name body out HN HB HO).
  - destruct (code_relation_total M (E_wal x (E_wn (native_named_raw_expression a))) env) as (all&HA).
    exact (raw_implication_nonzero_consequent M all (code_numeral M 1) out
      (raw_positive_tag_nonzero M 1 (zeroM M) (zeroM M) (code_numeral M 1)
        ltac:(discriminate) (raw_one_membership_graph M))
      (expression_implication_graph M env _ (CEconst 1) all (code_numeral M 1) out HA eq_refl HO)).
Qed.

Lemma source_two_common_bounds M a b :
  (exists k,source_bounded M a k) ->(exists k,source_bounded M b k) ->
  exists k,source_bounded M a k /\source_bounded M b k.
Proof.
  intros (k&HK) (l&HL). exists (addM M k l). split.
  - exact (source_bounded_monotone M a k (addM M k l) HK (coding_le_add M k l)).
  - apply (source_bounded_monotone M b l (addM M k l) HL). rewrite (add_comm M k l). apply coding_le_add.
Qed.

Theorem source_zfc_equivalent_binary_finite M h a b c d f g :
  (h=SFImpl \/h=SFAnd) ->
  (exists k,source_bounded M a k) ->(exists k,source_bounded M b k) ->
  (exists k,source_bounded M c k) ->(exists k,source_bounded M d k) ->
  source_zfc_equivalent M a c ->source_zfc_equivalent M b d ->
  sf_relation M h a b f ->sf_relation M h c d g ->source_zfc_equivalent M f g.
Proof.
  intros HH HA HB HC HD HI HJ HF HG.
  destruct (source_two_common_bounds M a b HA HB) as (k&HA'&HB').
  destruct (source_two_common_bounds M c d HC HD) as (l&HC'&HD').
  apply (source_zfc_equivalent_binary M h a b c d f g (addM M k l) HH);try assumption.
  - exact (source_bounded_monotone M a k (addM M k l) HA' (coding_le_add M k l)).
  - exact (source_bounded_monotone M b k (addM M k l) HB' (coding_le_add M k l)).
  - apply (source_bounded_monotone M c l (addM M k l) HC'). rewrite (add_comm M k l). apply coding_le_add.
  - apply (source_bounded_monotone M d l (addM M k l) HD'). rewrite (add_comm M k l). apply coding_le_add.
Qed.

Theorem source_zfc_equivalent_trans_finite M a b c :
  (exists k,source_bounded M a k) ->(exists k,source_bounded M b k) ->
  (exists k,source_bounded M c k) ->source_zfc_equivalent M a b ->
  source_zfc_equivalent M b c ->source_zfc_equivalent M a c.
Proof.
  intros HA HB HC HI HJ. destruct (source_two_common_bounds M a b HA HB) as (k&HA'&HB').
  destruct HC as (l&HC'). apply (source_zfc_equivalent_trans M a b c (addM M k l));try assumption.
  - exact (source_bounded_monotone M a k (addM M k l) HA' (coding_le_add M k l)).
  - exact (source_bounded_monotone M b k (addM M k l) HB' (coding_le_add M k l)).
  - apply (source_bounded_monotone M c l (addM M k l) HC'). rewrite (add_comm M k l). apply coding_le_add.
Qed.

Theorem source_zfc_equivalent_quantifier_finite M h a b qa qb :
  (h=SFAll \/h=SFEx) ->(exists k,source_bounded M a k) ->(exists k,source_bounded M b k) ->
  source_zfc_equivalent M a b ->sf_relation M h a (zeroM M) qa ->
  sf_relation M h b (zeroM M) qb ->source_zfc_equivalent M qa qb.
Proof.
  intros HH HA HB HI HQA HQB.
  destruct (source_two_common_bounds M a b HA HB) as (k&HA'&HB').
  exact (source_zfc_equivalent_quantifier M h a b qa qb k HH HA' HB' HI HQA HQB).
Qed.

Lemma source_binary_bound_exists M h a b f :sf_binary h ->sf_relation M h a b f ->
  (exists k,source_bounded M a k) ->(exists k,source_bounded M b k) ->exists k,source_bounded M f k.
Proof.
  intros HH HF HA HB. destruct (source_two_common_bounds M a b HA HB) as (k&HA'&HB'). exists k.
  apply (proj2 (source_bounded_accept_binary M h a b f k HH HF)). auto.
Qed.

Print Assumptions native_named_positive_nonzero.
Print Assumptions source_zfc_equivalent_binary_finite.
Print Assumptions source_zfc_equivalent_trans_finite.
