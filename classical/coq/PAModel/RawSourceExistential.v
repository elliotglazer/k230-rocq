(** Exact normalization of a raw encoded existential to the native source
    existential over its genuine binder-renamed matrix. Both raw1 slots
    remain diagonal membership atoms, including the slot inside the binder. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent
  NumericalProofs SetFormulaCodes SetCodeDescent SourceBounded SourceTraceBounds
  NumericalRenamingMaps NumericalRenaming NumericalContexts SourceSequents
  RawBinderRenaming RawSourceImage RawSourceImageInversion RawSourceImageBounds
  RawSourcePropositional RawEqualityCalibration RawLogicalRow1 SourceZFCProvability SourceZFCNoSelf
  SourceEncodedExistentialForward SourceEncodedExistentialReverse.
Unset Implicit Arguments.

Theorem raw_existential_source_normalization M x a neg all raw sa out rb rc matrix
    native forward reverse :
  implication_graph M a (code_numeral M 1) neg -> universal_graph M x neg all ->
  implication_graph M all (code_numeral M 1) raw ->
  raw_source_image M a sa ->raw_source_image M raw out ->
  raw_binder_renaming M x rb rc ->
  numerical_renaming M sa rb rc (succM M x) (succM M (zeroM M)) matrix ->
  sf_relation M SFEx matrix (zeroM M) native ->
  sf_relation M SFImpl out native forward ->sf_relation M SFImpl native out reverse ->
  source_zfc_provable M forward /\source_zfc_provable M reverse.
Proof.
  intros HNeg HAll HRaw HA HO HMap HMatrix HNative HF HV.
  pose proof (raw_positive_tag_nonzero M 1 (zeroM M) (zeroM M) (code_numeral M 1)
    ltac:(discriminate) (raw_one_membership_graph M)) as HOneN.
  pose proof (raw_implication_nonzero_consequent M a (code_numeral M 1) neg HOneN HNeg) as HNegN.
  pose proof (raw_implication_nonzero_consequent M all (code_numeral M 1) raw HOneN HRaw) as HRawN.
  destruct (raw_source_implication_inv M all (code_numeral M 1) raw out HRawN HRaw HO)
    as (sall&bad&HAllI&HBadI&HSRaw).
  destruct (raw_source_universal_inv M x neg all sall HAll HAllI)
    as (sneg&qb&qc&closedneg&HNegI&HMap'&HRNeg&HSAll).
  destruct (raw_source_implication_inv M a (code_numeral M 1) neg sneg HNegN HNeg HNegI)
    as (sa'&sbad&HA'&HSBad&HSNeg).
  rewrite (raw_source_image_functional M a sa' sa HA' HA) in HSNeg.
  apply (proj1 (numerical_renaming_binary M SFImpl sa sbad sneg qb qc
    (succM M x) (succM M (zeroM M)) closedneg ltac:(unfold sf_binary;auto) HSNeg)) in HRNeg.
  destruct HRNeg as (matrix'&closebad&HRMatrix&HRBad&HSMatrix).
  assert (EM:matrix' = matrix).
  { exact (numerical_renaming_functional_equivalent M sa qb qc (succM M x) rb rc (succM M x)
      (succM M (zeroM M)) matrix' matrix
      (raw_binder_renaming_equivalent M x qb qc rb rc HMap' HMap) HRMatrix HMatrix). }
  subst matrix'.
  apply (proj1 (numerical_renaming_member M (zeroM M) (zeroM M) sbad qb qc
    (succM M x) (succM M (zeroM M)) closebad (raw_one_source_member M sbad HSBad))) in HRBad.
  destruct HRBad as (d&d'&HD&HD'&HCloseBad).
  assert (ED:d' = d).
  { exact (renaming_lookup_functional M qb qc (succM M x) (succM M (zeroM M))
      (zeroM M) d' d HD' HD). }
  subst d'.
  destruct (raw_source_image_bounded M raw out HO) as (k&HBOut).
  destruct (proj1 (source_bounded_accept_binary M SFImpl sall bad out k
    ltac:(unfold sf_binary;auto) HSRaw) HBOut) as [HBAll HBBad].
  pose proof (proj1 (source_bounded_accept_unary M SFAll closedneg sall k
    (or_introl eq_refl) HSAll) HBAll) as HBCNeg.
  destruct (proj1 (source_bounded_accept_binary M SFImpl matrix closebad closedneg (succM M k)
    ltac:(unfold sf_binary;auto) HSMatrix) HBCNeg) as [HBMatrix HBCBad].
  pose proof (proj2 (source_bounded_accept_unary M SFEx matrix native k
    (or_intror eq_refl) HNative) HBMatrix) as HBNative.
  assert (HWNative:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) native).
  { exists k. split;[exact HBNative|apply context_bounded_empty]. }
  assert (HWF:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) forward).
  { exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_binary M SFImpl out native forward k
      ltac:(unfold sf_binary;auto) HF)). auto. }
  assert (HWV:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) reverse).
  { exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_binary M SFImpl native out reverse k
      ltac:(unfold sf_binary;auto) HV)). auto. }
  destruct (sf_relation_total M SFImpl bad (zeroM M)) as (notbad&HNotBad).
  destruct (sf_relation_total M SFImpl closebad (zeroM M)) as (notclosebad&HNotCloseBad).
  split.
  - exact (source_zfc_encoded_exists_forward M matrix native closebad closedneg sall bad out notbad forward
      HNative HSMatrix HSAll HSRaw HNotBad
      (source_zfc_no_self M (zeroM M) bad notbad (raw_one_source_member M bad HBadI) HNotBad)
      HF HWNative HWF).
  - exact (source_zfc_encoded_exists_reverse M matrix native closebad closedneg sall bad out notclosebad reverse
      HNative HSMatrix HSAll HSRaw HNotCloseBad
      (source_zfc_no_self M d closebad notclosebad HCloseBad HNotCloseBad) HV HWNative HWV).
Qed.

Theorem raw_existential_source_normalization_total M x a neg all raw sa out :
  implication_graph M a (code_numeral M 1) neg -> universal_graph M x neg all ->
  implication_graph M all (code_numeral M 1) raw ->
  raw_source_image M a sa ->raw_source_image M raw out ->
  exists rb rc matrix native forward reverse,
    raw_binder_renaming M x rb rc /\
    numerical_renaming M sa rb rc (succM M x) (succM M (zeroM M)) matrix /\
    sf_relation M SFEx matrix (zeroM M) native /\
    sf_relation M SFImpl out native forward /\sf_relation M SFImpl native out reverse /\
    source_zfc_provable M forward /\source_zfc_provable M reverse.
Proof.
  intros HN HQ HR HA HO.
  destruct (raw_binder_renaming_total M x) as (rb&rc&HMap).
  destruct (numerical_renaming_total M sa rb rc (succM M x) (succM M (zeroM M))) as (matrix&HM).
  destruct (sf_relation_total M SFEx matrix (zeroM M)) as (native&HNative).
  destruct (sf_relation_total M SFImpl out native) as (forward&HF).
  destruct (sf_relation_total M SFImpl native out) as (reverse&HV).
  exists rb,rc,matrix,native,forward,reverse. repeat first [assumption|split].
  all: pose proof (raw_existential_source_normalization M x a neg all raw sa out rb rc matrix
    native forward reverse HN HQ HR HA HO HMap HM HNative HF HV) as HP;tauto.
Qed.

Print Assumptions raw_existential_source_normalization.
Print Assumptions raw_existential_source_normalization_total.
