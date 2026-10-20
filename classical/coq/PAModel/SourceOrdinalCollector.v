(** Actual ZFR existence of the least-ordinal Replacement range and an
    ordinal upper envelope. No functionality, schema, or certificate
    premise remains; input coverage and monotonicity are separate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SetSchemaConstructors SchemaRenamingDescriptors SourceFunctionalityShells
  SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceOrdinalCollectionZFRFunctionality
  SourceReplacementCollector SourceOrdinalEnvelope SourceOrdinalUnion SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_oc_collector_total M phi oc count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  exists a b c functionality profile collector,
    schema_renaming M RepA oc a /\schema_renaming M RepB oc b /\schema_renaming M RepC oc c /\
    source_functionality_graph M a b functionality /\
    source_replacement_profile_graph M c profile /\sf_relation M SFEx profile (zeroM M) collector /\
    source_zfr_provable M collector.
Proof.
  intros HB HOC.
  destruct (schema_renaming_total M RepA oc) as (a&HA).
  destruct (schema_renaming_total M RepB oc) as (b&HBB).
  destruct (schema_renaming_total M RepC oc) as (c&HC).
  destruct (code_relation_total M (E_sf_functionality (CEvar 0) (CEvar 1))
    (schema_env3 a b (zeroM M))) as (functionality&HF).
  pose proof (source_zfr_oc_functionality M phi oc a b functionality count HB HOC HA HBB HF) as PF.
  pose proof (source_oc_form_bounded M _ phi oc count (source_ordinal_predicate_bounded M) HB HOC) as HOCBound.
  destruct (source_zfr_replacement_collector M oc count a b c functionality HOCBound HA HBB HC HF PF)
    as (profile&collector&HProfile&HCollector&PCollector).
  exists a,b,c,functionality,profile,collector.
  split;[exact HA|]. split;[exact HBB|]. split;[exact HC|]. split;[exact HF|].
  split;[exact HProfile|]. split;[exact HCollector|exact PCollector].
Qed.

Theorem source_zfr_oc_upper_envelope_total M phi oc count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  exists c profile collector upper decorated envelope,
    schema_renaming M RepC oc c /\source_replacement_profile_graph M c profile /\
    sf_relation M SFEx profile (zeroM M) collector /\source_zfr_provable M collector /\
    source_ordinal_upper_graph M upper /\sf_relation M SFAnd profile upper decorated /\
    sf_relation M SFEx decorated (zeroM M) envelope /\source_zfr_provable M envelope.
Proof.
  intros HB HOC.
  destruct (source_zfr_oc_collector_total M phi oc count HB HOC)
    as (a&b&c&functionality&profile&collector&HA&HBB&HC&HF&HProfile&HCollector&PCollector).
  destruct (source_zfr_oc_ordinal_envelope M phi oc c profile collector HOC HC HProfile HCollector PCollector)
    as (upper&decorated&envelope&HUpper&HDecorated&HEnvelope&PEnvelope).
  exists c,profile,collector,upper,decorated,envelope.
  split;[exact HC|]. split;[exact HProfile|]. split;[exact HCollector|]. split;[exact PCollector|].
  split;[exact HUpper|]. split;[exact HDecorated|]. split;[exact HEnvelope|exact PEnvelope].
Qed.

Print Assumptions source_zfr_oc_collector_total.
Print Assumptions source_zfr_oc_upper_envelope_total.

