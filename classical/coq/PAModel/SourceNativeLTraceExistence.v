(** The native carrier trace-existence image is supplied by actual L-schema proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalContexts NumericalSourceFull ContextCombination
 SourceBounded SourceRelativization SourceDomainContexts SourceLFixed SourceZFRProvability SourceKZFCForwardSchemas
 SourceLOpenProofTransfer SourceUpperTraceProfile SourceUpperTraceExists SourceDescriptorClosure SourceSetTheoryDescriptors NumericalRenaming.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_zfr_L_upper_trace_exists M phi count profile exprofile relative:
 L_separation_image_obligation M ->L_replacement_image_obligation M ->
 source_bounded M phi(succM M(succM M count)) ->source_upper_trace_profile M phi profile ->
 sf_relation M SFEx profile(zeroM M)exprofile ->source_relativization M(source_L_domain_code M)exprofile relative ->
 exists bound tb tc tn,source_zfr_context M tb tc tn /\
 forall k db dc ub uc un,coding_lt M bound(succM M k) ->source_domain_context M(source_L_domain_code M)k db dc ->
 context_union M tb tc tn db dc k ub uc un ->source_full_prv M ub uc un relative.
Proof.
 intros HS HR HP HProfile HEx HRelative.
 exact(source_zfr_L_open_proof_from_schemas M exprofile relative HS HR HRelative
  (source_zfr_upper_trace_exists M phi count profile exprofile HP HProfile HEx)).
Qed.
Print Assumptions source_zfr_L_upper_trace_exists.

Theorem source_zfr_L_upper_trace_renamed_exists M phi count profile exprofile renamed rb rc rn delta relative:
 L_separation_image_obligation M ->L_replacement_image_obligation M ->
 source_bounded M phi(succM M(succM M count)) ->source_upper_trace_profile M phi profile ->
 sf_relation M SFEx profile(zeroM M)exprofile ->numerical_renaming M exprofile rb rc rn delta renamed ->
 source_relativization M(source_L_domain_code M)renamed relative ->
 exists bound tb tc tn,source_zfr_context M tb tc tn /\
 forall k db dc ub uc un,coding_lt M bound(succM M k) ->source_domain_context M(source_L_domain_code M)k db dc ->
 context_union M tb tc tn db dc k ub uc un ->source_full_prv M ub uc un relative.
Proof.
 intros HS HR HP HProfile HEx HShift HRelative.
 apply(source_zfr_L_open_proof_from_schemas M renamed relative HS HR HRelative).
 apply(proj1(source_zfr_descriptor_provable M renamed)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor exprofile rb rc rn delta renamed
  (proj2(source_zfr_descriptor_provable M exprofile)(source_zfr_upper_trace_exists M phi count profile exprofile HP HProfile HEx))HShift).
Qed.
Print Assumptions source_zfr_L_upper_trace_renamed_exists.
