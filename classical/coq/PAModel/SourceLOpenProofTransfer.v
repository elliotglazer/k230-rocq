(** Concrete open L-relative proof construction from the existing L schema images. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalContexts NumericalSourceFull ContextCombination
 SourceBounded SourceDescriptorRelativeTransfer SourceOpenRelativeProofTransfer SourceSetTheoryDescriptors
 SourceLFixed SourceZFRProvability SourceKZFCForwardSchemas NumericalZFRAxioms SourceRelativization SourceDomainContexts.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_zfr_L_open_proof_from_schemas M f relative:
 L_separation_image_obligation M ->L_replacement_image_obligation M ->
 source_relativization M(source_L_domain_code M)f relative ->source_zfr_provable M f ->
 exists bound tb tc tn,source_zfr_context M tb tc tn /\
 forall k db dc ub uc un,coding_lt M bound(succM M k) ->source_domain_context M(source_L_domain_code M)k db dc ->
 context_union M tb tc tn db dc k ub uc un ->source_full_prv M ub uc un relative.
Proof.
 intros HS HR HRel PSource.
 assert(HImages:source_descriptor_relative_axiom_images M ZFRSourceDescriptor ZFRSourceDescriptor(source_L_domain_code M)).
 { intros a HA _. destruct(L_axiom_images_from_uniform_schemas M HS HR a
    (numerical_zfr_source_axiom_in_zfc M a(proj1(ZFRSourceDescriptor_axiom M a)HA)))as(ra&HRA&PRA).
   exists ra. split;[exact HRA|exact(proj2(source_zfr_descriptor_provable M ra)PRA)]. }
 destruct(source_descriptor_open_relative_proof_transfer M ZFRSourceDescriptor ZFRSourceDescriptor(source_L_domain_code M)f relative
  (numerical_L_domain_bounded M)HImages HRel(proj2(source_zfr_descriptor_provable M f)PSource))as(bound&tb&tc&tn&HT&HP).
 exists bound,tb,tc,tn. split;[exact(proj1(source_zfr_descriptor_context M tb tc tn)HT)|exact HP].
Qed.
Print Assumptions source_zfr_L_open_proof_from_schemas.
