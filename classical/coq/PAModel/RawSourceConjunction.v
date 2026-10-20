(** Native conjunction is provably equivalent to the actual raw encoded
    conjunction image. The matrix holes are arbitrary internal source codes;
    encoded falsity is a genuine diagonal membership atom, refuted by the
    actual source Foundation proof. No syntactic identification with0 occurs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent NumericalProofs
  SetFormulaCodes SetCodeDescent SourceBounded SourceTraceBounds NumericalContexts NumericalSourceFull
  SourcePropositionalTemplates SourceConjunctionPrograms SourceZFCProvability SourceZFCBasicClosure SourceZFCNoSelf
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawSourcePropositional RawEqualityCalibration RawLogicalRow1.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_encoded_conjunction_template M a b bad nb inner encoded :
  sf_relation M SFImpl b bad nb ->sf_relation M SFImpl a nb inner ->
  sf_relation M SFImpl inner bad encoded ->
  code_relation M (code_parameters a b bad (zeroM M))
    (source_prop_expression (SPTEncodedAnd (SPTSlot 0) (SPTSlot 1) (SPTSlot 2))) encoded.
Proof.
  intros HNB HI HE.
  apply (source_prop_template_join M _ SFImpl
    (SPTImpl (SPTSlot 0) (SPTImpl (SPTSlot 1) (SPTSlot 2))) (SPTSlot 2) inner bad encoded);
    [|reflexivity|exact HE].
  apply (source_prop_template_join M _ SFImpl (SPTSlot 0)
    (SPTImpl (SPTSlot 1) (SPTSlot 2)) a nb inner);[reflexivity| |exact HI].
  exact (source_prop_template_join M _ SFImpl (SPTSlot 1) (SPTSlot 2) b bad nb eq_refl eq_refl HNB).
Qed.

Theorem source_zfc_encoded_conjunction_normalization M a b bad nb inner encoded native forward reverse x k :
  source_bounded M a k ->source_bounded M b k ->source_bounded M bad k ->
  sf_relation M SFMember x x bad ->
  sf_relation M SFImpl b bad nb ->sf_relation M SFImpl a nb inner ->
  sf_relation M SFImpl inner bad encoded ->sf_relation M SFAnd a b native ->
  sf_relation M SFImpl encoded native forward ->sf_relation M SFImpl native encoded reverse ->
  source_zfc_provable M forward /\source_zfc_provable M reverse.
Proof.
  intros HA HB HBad HBD HNB HI HE HC HForward HReverse.
  set (rho:=code_parameters a b bad (zeroM M)).
  assert (HEnv:forall i,source_bounded M (rho i) k).
  { intros [|[|[|i]]];cbn [rho code_parameters];try assumption;apply source_bounded_accept_falsity. }
  pose proof (source_encoded_conjunction_template M a b bad nb inner encoded HNB HI HE) as HEncoded.
  assert (HNative:code_relation M rho (source_prop_expression (SPTAnd (SPTSlot 0) (SPTSlot 1))) native).
  { exact (source_prop_template_join M rho SFAnd (SPTSlot 0) (SPTSlot 1) a b native eq_refl eq_refl HC). }
  destruct (sf_relation_total M SFImpl bad (zeroM M)) as (neg&HNeg).
  destruct (source_zfc_no_self M x bad neg HBD HNeg) as (cb&cc&cn&HCtx&PNeg).
  assert (HCtxBound:context_bounded M cb cc cn k).
  { exact (context_bounded_monotone M cb cc cn (zeroM M) k
      (source_zfc_context_closed M cb cc cn HCtx) (coding_zero_lt_succ M k)). }
  assert (HNegCode:code_relation M rho (source_prop_expression (SPTImpl (SPTSlot 2) SPTFalse)) neg).
  { exact (source_prop_template_join M rho SFImpl (SPTSlot 2) SPTFalse bad (zeroM M) neg eq_refl eq_refl HNeg). }
  split.
  - exists cb,cc,cn. split;[exact HCtx|].
    apply (source_prop_program_sound M _ _ source_encoded_conjunction_program rho k cb cc cn forward HEnv HCtxBound).
    + intros p [<-|[]] f HF. rewrite (code_relation_functional M _ rho f neg HF HNegCode). exact PNeg.
    + exact (source_prop_template_join M rho SFImpl
        (SPTEncodedAnd (SPTSlot 0) (SPTSlot 1) (SPTSlot 2))
        (SPTAnd (SPTSlot 0) (SPTSlot 1)) encoded native forward HEncoded HNative HForward).
  - apply source_zfc_provable_from_empty.
    apply (source_prop_program_sound M _ _ source_native_conjunction_program rho k
      (zeroM M) (zeroM M) (zeroM M) reverse HEnv (context_bounded_empty M (zeroM M) (zeroM M) k)).
    + intros p HP. contradiction.
    + exact (source_prop_template_join M rho SFImpl
        (SPTAnd (SPTSlot 0) (SPTSlot 1))
        (SPTEncodedAnd (SPTSlot 0) (SPTSlot 1) (SPTSlot 2)) native encoded reverse HNative HEncoded HReverse).
Qed.

Theorem raw_conjunction_source_normalization M a b nb inner raw sa sb out native forward reverse :
  implication_graph M b (code_numeral M 1) nb ->implication_graph M a nb inner ->
  implication_graph M inner (code_numeral M 1) raw ->
  raw_source_image M a sa ->raw_source_image M b sb ->raw_source_image M raw out ->
  sf_relation M SFAnd sa sb native ->sf_relation M SFImpl out native forward ->
  sf_relation M SFImpl native out reverse ->
  source_zfc_provable M forward /\source_zfc_provable M reverse.
Proof.
  intros HNB HI HR HA HB HO HC HF HV.
  pose proof (raw_positive_tag_nonzero M 1 (zeroM M) (zeroM M) (code_numeral M 1)
    ltac:(discriminate) (raw_one_membership_graph M)) as HOne.
  pose proof (raw_implication_nonzero_consequent M b _ nb HOne HNB) as HNBN.
  pose proof (raw_implication_nonzero_consequent M a nb inner HNBN HI) as HIN.
  pose proof (raw_implication_nonzero_consequent M inner _ raw HOne HR) as HRN.
  destruct (raw_source_implication_inv M inner _ raw out HRN HR HO) as (si&bad&HSI&HBad&HEnc).
  destruct (raw_source_implication_inv M a nb inner si HIN HI HSI) as (sa'&snb&HA'&HNBI&HSInner).
  rewrite (raw_source_image_functional M a sa' sa HA' HA) in HSInner.
  destruct (raw_source_implication_inv M b _ nb snb HNBN HNB HNBI) as (sb'&bad'&HB'&HBad'&HSNB).
  rewrite (raw_source_image_functional M b sb' sb HB' HB) in HSNB.
  rewrite (raw_source_image_functional M _ bad' bad HBad' HBad) in HSNB.
  destruct (raw_source_image_bounded M raw out HO) as (k&HBound).
  destruct (proj1 (source_bounded_accept_binary M SFImpl si bad out k
    ltac:(unfold sf_binary;auto) HEnc) HBound) as [HBI HBBad].
  destruct (proj1 (source_bounded_accept_binary M SFImpl sa snb si k
    ltac:(unfold sf_binary;auto) HSInner) HBI) as [HBSA HBNotB].
  destruct (proj1 (source_bounded_accept_binary M SFImpl sb bad snb k
    ltac:(unfold sf_binary;auto) HSNB) HBNotB) as [HBSB _].
  exact (source_zfc_encoded_conjunction_normalization M sa sb bad snb si out native forward reverse
    (zeroM M) k HBSA HBSB HBBad (raw_one_source_member M bad HBad) HSNB HSInner HEnc HC HF HV).
Qed.

Print Assumptions source_zfc_encoded_conjunction_normalization.
Print Assumptions raw_conjunction_source_normalization.
