(** The equal-role fixed background holds in the exact pinned L class,
    by an actual finite proof and only the already checked fixed L images. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceNumeralLift SourceFiniteContexts NumericalContexts NumericalSourceFull NumericalTheories
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes SourceAxiomContexts SourceDescriptorProvability
  SourceSetTheoryDescriptors SourceZFRProvability SourceImageContextWitnesses
  SourceRelativeTheoryTransfer SourceRelativization SourceRelativizationBounds
  NativeKUniformClosedImplication NativeEqualFiniteBackground SourceLFixed SourceLNonempty
  SourceLFixedImages NumericalWFNonempty.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma native_L_nonempty_graph M:sf_relation M SFEx (source_L_domain_code M)(zeroM M)(source_L_nonempty_code M).
Proof. exact(source_formula_ex_numeral M source_L_domain). Qed.
Local Opaque source_L_domain_code source_L_nonempty_code.

Theorem numerical_L_native_equal_background M background relative :
  native_equal_background M background ->
  source_relativization M (source_L_domain_code M) background relative ->
  source_zfr_provable M relative.
Proof.
  intros HB HR.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(native_L_nonempty_graph M) as HEx.
  destruct(numerical_L_nonempty_zfr M) as(eb&ec&en&HE&PE).
  pose proof(proj2(source_zfr_descriptor_context M eb ec en) HE) as HEDescriptor.
  destruct(source_model_context_total M native_equal_fixed_background) as(b&c&n&HC).
  pose proof(numerical_native_equal_background M b c n background HC HB) as PBackground.
  destruct(source_axiom_image_context_collect_witnesses_with_proof M ZFRSourceDescriptor
    (source_L_domain_code M) b c n eb ec en (source_L_nonempty_code M) HEDescriptor PE)
    as(ub&uc&un&HUC&PUEx&HImages).
  - intros f HF. apply(proj1(source_model_context_member_iff M b c n native_equal_fixed_background f HC)) in HF.
    destruct HF as(phi&HIn&->).
    assert(HFixed:exists tag,phi=zfc_fixed_source tag).
    { unfold native_equal_fixed_background in HIn. destruct HIn as[<-|[<-|[<-|[]]]];
        [exists ZFCEmpty|exists ZFCPair|exists ZFCRefl];reflexivity. }
    destruct HFixed as(tag&->).
    destruct(source_relativization_total M (source_L_domain_code M)
      (code_numeral M(sf_encode(zfc_fixed_source tag)))) as(rf&HRF).
    destruct(numerical_L_fixed_axiom_images M tag _ rf
      (source_formula_numeral_graph M(zfc_fixed_source tag)) HRF) as(tb&tc&tn&HT&PT).
    exists rf,tb,tc,tn. split;[exact HRF|]. split;[|exact PT].
    exact(proj2(source_zfr_descriptor_context M tb tc tn) HT).
  - exists ub,uc,un. split.
    + exact(proj1(source_zfr_descriptor_context M ub uc un) HUC).
    + exact(source_relative_proof_transfer M (source_L_domain_code M)(source_L_nonempty_code M)
        ub uc un b c n background relative (proj1 HUC) HD HEx PUEx
        (source_relativization_preserves_bound M background (source_L_domain_code M)(zeroM M) relative
          HD (native_equal_background_closed M background HB) HR) HR HImages PBackground).
Qed.

Print Assumptions numerical_L_native_equal_background.
