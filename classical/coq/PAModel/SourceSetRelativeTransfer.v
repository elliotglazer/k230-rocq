(** Concrete consumers for the remaining WF/L interpretation inputs.
    Axiom images and domain nonemptiness are ordinary actual source-theory
    proof premises; no shared context or proof-transfer premise occurs. *)
From PAModel Require Import Model CodeExpressions NumericalContexts SetFormulaCodes SourceBounded
  NumericalCoreAxioms NumericalZFCAxioms NumericalZFRAxioms NumericalSourceFull
  SourceRelativization SourceDescriptorProvability SourceDescriptorRelativeTransfer
  SourceSetTheoryDescriptors SourceZFRProvability CoreConsistencyReduction SourceZFCProvability.
Unset Implicit Arguments.

Theorem source_zfc_relative_refutation_to_zfr M domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex -> source_zfr_provable M ex ->
  (forall f,numerical_zfc_source_axiom M f -> exists rf,
    source_relativization M domain f rf /\ source_zfr_provable M rf) ->
  source_zfc_provable M (zeroM M) -> source_zfr_provable M (zeroM M).
Proof.
  intros HD HE PE HI HP.
  apply (proj1 (source_zfr_descriptor_provable M (zeroM M))).
  apply (source_descriptor_relative_refutation_transfer M ZFCSourceDescriptor ZFRSourceDescriptor domain ex HD HE).
  - exact (proj2 (source_zfr_descriptor_provable M ex) PE).
  - intros f HF HB. destruct (HI f (proj1 (ZFCSourceDescriptor_axiom M f) HF)) as (rf & HR & PR).
    exists rf. split;[exact HR|]. exact (proj2 (source_zfr_descriptor_provable M rf) PR).
  - exact (proj2 (source_zfc_descriptor_provable M (zeroM M)) HP).
Qed.

Theorem source_zfr_relative_refutation_to_core M domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex -> source_core_provable M ex ->
  (forall f,numerical_zfr_source_axiom M f -> exists rf,
    source_relativization M domain f rf /\ source_core_provable M rf) ->
  source_zfr_provable M (zeroM M) -> source_core_provable M (zeroM M).
Proof.
  intros HD HE PE HI HP.
  apply (proj1 (source_core_descriptor_provable M (zeroM M))).
  apply (source_descriptor_relative_refutation_transfer M ZFRSourceDescriptor CoreSourceDescriptor domain ex HD HE).
  - exact (proj2 (source_core_descriptor_provable M ex) PE).
  - intros f HF HB. destruct (HI f (proj1 (ZFRSourceDescriptor_axiom M f) HF)) as (rf & HR & PR).
    exists rf. split;[exact HR|]. exact (proj2 (source_core_descriptor_provable M rf) PR).
  - exact (proj2 (source_zfr_descriptor_provable M (zeroM M)) HP).
Qed.

Theorem source_zfc_relative_refutation_to_core M wf wfex l lex :
  source_bounded M wf (code_numeral M 1) ->
  sf_relation M SFEx wf (zeroM M) wfex -> source_core_provable M wfex ->
  (forall f,numerical_zfr_source_axiom M f -> exists rf,
    source_relativization M wf f rf /\ source_core_provable M rf) ->
  source_bounded M l (code_numeral M 1) ->
  sf_relation M SFEx l (zeroM M) lex -> source_zfr_provable M lex ->
  (forall f,numerical_zfc_source_axiom M f -> exists rf,
    source_relativization M l f rf /\ source_zfr_provable M rf) ->
  source_zfc_provable M (zeroM M) -> source_core_provable M (zeroM M).
Proof.
  intros HW EW PW IW HL EL PL IL HP.
  exact (source_zfr_relative_refutation_to_core M wf wfex HW EW PW IW
    (source_zfc_relative_refutation_to_zfr M l lex HL EL PL IL HP)).
Qed.

Corollary source_core_consistency_implies_zfc_via_relative_images M wf wfex l lex :
  source_bounded M wf (code_numeral M 1) ->
  sf_relation M SFEx wf (zeroM M) wfex -> source_core_provable M wfex ->
  (forall f,numerical_zfr_source_axiom M f -> exists rf,
    source_relativization M wf f rf /\ source_core_provable M rf) ->
  source_bounded M l (code_numeral M 1) ->
  sf_relation M SFEx l (zeroM M) lex -> source_zfr_provable M lex ->
  (forall f,numerical_zfc_source_axiom M f -> exists rf,
    source_relativization M l f rf /\ source_zfr_provable M rf) ->
  source_core_consistent M -> source_zfc_consistent M.
Proof.
  intros HW EW PW IW HL EL PL IL HC HZ.
  exact (HC (source_zfc_relative_refutation_to_core M wf wfex l lex HW EW PW IW HL EL PL IL HZ)).
Qed.

Print Assumptions source_zfc_relative_refutation_to_zfr.
Print Assumptions source_zfr_relative_refutation_to_core.
Print Assumptions source_zfc_relative_refutation_to_core.
Print Assumptions source_core_consistency_implies_zfc_via_relative_images.
