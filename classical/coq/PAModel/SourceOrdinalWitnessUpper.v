(** Actual pointwise coverage of a least-ordinal Replacement range: the
    least witness is a range member and is a subset of the chosen upper
    ordinal. Ordinary proofs supply the range, input and upper profile. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenaming SchemaRenamingDescriptors NumericalSourceFull
  SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceReplacementMemberAt
  SourceOrdinalWitnessRange SourceOrdinalUpperMembers.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_oc_witness_upper M b c n phi oc matrix leastbody profile count s x u input upper :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->schema_renaming M RepC oc matrix ->
  numerical_renaming M oc (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody ->
  source_replacement_profile_at_graph M s x matrix profile ->
  sf_relation M SFMember (code_numeral M 1) x input ->source_oc_upper_point_graph M s u upper ->
  source_full_prv M b c n profile ->source_full_prv M b c n input ->
  source_full_prv M b c n leastbody ->source_full_prv M b c n upper ->
  exists member subset,sf_relation M SFMember (zeroM M) s member /\
    source_oc_subset_graph M (zeroM M) u subset /\source_full_prv M b c n member /\
    source_full_prv M b c n subset /\source_full_prv M b c n (source_ordinal_predicate_code M) /\
    source_full_prv M b c n phi.
Proof.
  intros HB HO HM HR HP HI HU PP PI PW PU.
  destruct (sf_relation_total M SFMember (zeroM M) s) as (member&HMember).
  destruct (source_oc_subset_total M (zeroM M) u) as (subset&HSubset).
  pose proof (source_full_oc_witness_member M b c n phi oc matrix leastbody profile count s x input member
    HB HO HM HR HP HI HMember PP PI PW) as PM.
  pose proof (source_full_oc_upper_member M b c n s u (zeroM M) upper member subset
    HU HMember HSubset PU PM) as PS.
  destruct (source_full_oc_witness_payload M b c n phi oc leastbody (succM M (succM M count))
    HB HO HR PW) as (POrd&Phi).
  exists member,subset. split;[exact HMember|]. split;[exact HSubset|].
  split;[exact PM|]. split;[exact PS|auto].
Qed.

Print Assumptions source_full_oc_witness_upper.
