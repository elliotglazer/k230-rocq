(** A genuine internally coded range-set existence proof obtained from
    the actual Replacement schema and an ordinary functionality proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SchemaRenamingDescriptors SourceFunctionalityShells
  SourcePropositionalRebase SourceWFSeparationConstructor SourceZFRProvability
  SourceZFRReplacementUse SourceSetTheoryDescriptors SourceDescriptorAllBody.
Unset Implicit Arguments.

Definition E_source_replacement_profile theta := E_sf_all
  (E_sf_iff (E_sf_mem 0 1) (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3) theta))).
Definition source_replacement_profile_graph M matrix profile :=
  code_relation M (fun _=>matrix) (E_source_replacement_profile (CEvar 0)) profile.

Theorem source_zfr_replacement_collector M phi count a b c functionality :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi a ->schema_renaming M RepB phi b ->schema_renaming M RepC phi c ->
  source_functionality_graph M a b functionality ->source_zfr_provable M functionality ->
  exists profile collector,source_replacement_profile_graph M c profile /\
    sf_relation M SFEx profile (zeroM M) collector /\source_zfr_provable M collector.
Proof.
  intros HB HA HBB HC HF PF.
  destruct (source_zfr_replacement_range M phi count a b c functionality HB HA HBB HC HF PF)
    as (range&HRange&PRange).
  unfold source_replacement_range_graph,E_source_replacement_range in HRange.
  destruct (schema_expression_quantifier_split M _ SFAll _ range HRange)
    as (collector&HCollector&HAll).
  destruct (schema_expression_quantifier_split M _ SFEx _ collector HCollector)
    as (profile&HProfile&HEx).
  exists profile,collector. split;[exact HProfile|]. split;[exact HEx|].
  apply (proj1 (source_zfr_descriptor_provable M collector)).
  exact (source_descriptor_provable_all_body M ZFRSourceDescriptor collector range HAll
    (proj2 (source_zfr_descriptor_provable M range) PRange)).
Qed.

Print Assumptions source_zfr_replacement_collector.
