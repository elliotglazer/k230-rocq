(** Construct the exact least-ordinal range graph after one fresh free
    variable, eliminating all lifted-map and shifted-matrix witnesses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming SourceFiniteCutoffShift SchemaRenamingDescriptors
  SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceOrdinalCollectionCutoff
  SourceReplacementMemberAt SourceReplacementProfileShift SourceQuantifierRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_oc_profile_advance M phi oc matrix profile s x count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->schema_renaming M RepC oc matrix ->
  source_replacement_profile_at_graph M s x matrix profile ->
  exists phi' oc' matrix' profile',source_cutoff_shift M 2 phi phi' /\
    source_cutoff_shift M 2 oc oc' /\source_oc_form M (source_ordinal_predicate_code M) phi' oc' /\
    schema_renaming M RepC oc' matrix' /\
    source_replacement_profile_at_graph M (succM M s) (succM M x) matrix' profile' /\
    source_formula_shift M profile profile'.
Proof.
  intros HB HO HM HP.
  destruct (source_cutoff_shift_total M 2 phi) as (phi'&HCut).
  destruct (source_cutoff_shift_total M 2 oc) as (oc'&HCutOC).
  pose proof (source_oc_form_bounded M _ phi oc count (source_ordinal_predicate_bounded M) HB HO) as HOCBound.
  pose proof (source_oc_form_cutoff_two M phi phi' oc oc' (succM M (succM M count))
    HB HO HCut HCutOC) as HO'.
  destruct (renaming_lift_total M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (ab&ac&an&HL1).
  destruct (renaming_lift_total M ab ac an (code_numeral M 1)) as (rb&rc&rn&HL2).
  destruct (numerical_renaming_total M matrix rb rc rn (code_numeral M 1)) as (matrix'&HRM).
  pose proof (source_repc_cutoff_two_shift M oc matrix oc' matrix' (succM M (succM M count))
    ab ac an rb rc rn HOCBound HM HCutOC HL1 HL2 HRM) as HM'.
  destruct (code_relation_total M E_replacement_profile_at
    (replacement_profile_at_environment (succM M s) (succM M x) matrix')) as (profile'&HP').
  pose proof (source_replacement_profile_shift M s x matrix profile matrix' profile'
    ab ac an rb rc rn HP HL1 HL2 HRM HP') as HShift.
  exists phi',oc',matrix',profile'. split;[exact HCut|]. split;[exact HCutOC|].
  split;[exact HO'|]. split;[exact HM'|]. split;[exact HP'|exact HShift].
Qed.

Print Assumptions source_oc_profile_advance.
