(** Actual source ZFC image of exists a (forall a B) -> B.  Repeated
    binders are proved vacuous by the internal renaming diamond, while
    the raw code0 truth collision and raw code1 diagonal atom stay explicit. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent NumericalProofs ProofTemplates
  SetFormulaCodes SetCodeDescent NumericalRenaming NumericalContexts
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawSourcePropositional RawEqualityCalibration
  RawBinderSelfSpecialization RawBinderShadowing SourceZFCNoSelf SourceZFCProvability
  SourceVacuousEncodedExistential RawLogicalRow1.
Unset Implicit Arguments.

Theorem raw_exists_universal_graph_source M a body quantified neg outer_all encoded raw out :
  universal_graph M a body quantified -> implication_graph M quantified (code_numeral M 1) neg ->
  universal_graph M a neg outer_all -> implication_graph M outer_all (code_numeral M 1) encoded ->
  implication_graph M encoded body raw -> raw_source_image M raw out -> source_zfc_provable M out.
Proof.
  intros HQ HNeg HAll HE HRaw HO.
  pose proof (raw_positive_tag_nonzero M 1 (zeroM M) (zeroM M) (code_numeral M 1)
    ltac:(discriminate) (raw_one_membership_graph M)) as HOneN.
  pose proof (raw_implication_nonzero_consequent M quantified (code_numeral M 1) neg HOneN HNeg) as HNegN.
  pose proof (raw_implication_nonzero_consequent M outer_all (code_numeral M 1) encoded HOneN HE) as HEN.
  assert (HRN:raw<>zeroM M).
  { intro E. subst raw. exact (HEN (proj1 (raw_zero_implication_arguments M encoded body HRaw))). }
  destruct (raw_source_implication_inv M encoded body raw out HRN HRaw HO)
    as (se&sb&HEI&HBI&HSOut).
  destruct (raw_source_implication_inv M outer_all (code_numeral M 1) encoded se HEN HE HEI)
    as (sa&bad0&HAI&HBad0I&HSE).
  destruct (raw_source_universal_inv M a neg outer_all sa HAll HAI)
    as (sneg&rb&rc&matrix&HNI&HMapOuter&HRNeg&HSA).
  destruct (raw_source_implication_inv M quantified (code_numeral M 1) neg sneg HNegN HNeg HNI)
    as (sq&sbad&HQI&HBadI&HSNeg).
  apply (proj1 (numerical_renaming_binary M SFImpl sq sbad sneg rb rc (succM M a)
    (succM M (zeroM M)) matrix ltac:(unfold sf_binary;auto) HSNeg)) in HRNeg.
  destruct HRNeg as (shifted&closebad&HRQ&HRBad&HSMatrix).
  destruct (raw_source_universal_inv M a body quantified sq HQ HQI)
    as (sb'&qb&qc&closed&HBI'&HMapInner&HRBody&HSQ).
  rewrite (raw_source_image_functional M body sb' sb HBI' HBI) in HRBody.
  destruct (raw_source_image_bounded M body sb HBI) as (k&HB).
  pose proof (raw_binder_self_instantiation M a sb closed k qb qc HB HMapInner HRBody) as HInst.
  pose proof (raw_binder_quantified_shadowing M a sb closed sq shifted k qb qc rb rc
    HB HMapInner HRBody HSQ HMapOuter HRQ) as HShift.
  destruct (sf_relation_total M SFImpl bad0 (zeroM M)) as (notbad&HNot).
  apply (source_zfc_vacuous_encoded_exists M sb closed sq shifted bad0 closebad
    notbad matrix sa se a out HSQ HInst HShift HSMatrix HSA HSE HNot).
  - exact (source_zfc_no_self M (zeroM M) bad0 notbad (raw_one_source_member M bad0 HBad0I) HNot).
  - exact HSOut.
  - destruct (raw_source_image_bounded M quantified sq HQI) as (l&HL).
    exists l. split;[exact HL|apply context_bounded_empty].
  - destruct (raw_source_image_bounded M raw out HO) as (l&HL).
    exists l. split;[exact HL|apply context_bounded_empty].
Qed.

Theorem source_zfc_raw_row6 M env raw out :
  code_relation M env code_row6 raw -> raw_source_image M raw out -> source_zfc_provable M out.
Proof.
  intros HR HO.
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 1)) env) as (quantified&HQ).
  destruct (code_relation_total M (E_wn (E_wal (CEvar 0) (CEvar 1))) env) as (neg&HN).
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wn (E_wal (CEvar 0) (CEvar 1)))) env)
    as (outer_all&HA).
  destruct (code_relation_total M (E_wex (CEvar 0) (E_wal (CEvar 0) (CEvar 1))) env) as (encoded&HE).
  apply (raw_exists_universal_graph_source M (env 0) (env 1) quantified neg outer_all encoded raw out).
  - exact (expression_universal_graph M env (CEvar 0) (CEvar 1) _ _ quantified eq_refl eq_refl HQ).
  - exact (expression_implication_graph M env (E_wal (CEvar 0) (CEvar 1)) (CEconst 1)
      quantified (code_numeral M 1) neg HQ eq_refl HN).
  - exact (expression_universal_graph M env (CEvar 0) (E_wn (E_wal (CEvar 0) (CEvar 1)))
      _ neg outer_all eq_refl HN HA).
  - exact (expression_implication_graph M env
      (E_wal (CEvar 0) (E_wn (E_wal (CEvar 0) (CEvar 1)))) (CEconst 1)
      outer_all (code_numeral M 1) encoded HA eq_refl HE).
  - exact (expression_implication_graph M env (E_wex (CEvar 0) (E_wal (CEvar 0) (CEvar 1)))
      (CEvar 1) encoded (env 1) raw HE eq_refl HR).
  - exact HO.
Qed.

Print Assumptions raw_exists_universal_graph_source.
Print Assumptions source_zfc_raw_row6.
