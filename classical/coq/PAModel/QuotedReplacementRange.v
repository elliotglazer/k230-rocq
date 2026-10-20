(** The outer input-set universal quantifier of source Replacement. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs NumericalQuotation
  NumericalEnvironments NumericalContexts ContextualProofs StableContextSupport NamedLeibnizSteps
  QuotationHygiene QuotationPayloads QuotationSchemaSkeleton QuotedSameBaseRules
  SetSchemaConstructors SchemaRenamingDescriptors SourceBounded RawQuotientAtomCongruence
  RawCollectionProfile ReplacementFreshAllocation ContextFreshBounds
  ReplacementPointwiseSkeleton QuotedReplacementOutput QuotedReplacementCollector ArbitraryWitnessIntroduction.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem quoted_replacement_range_from_raw_collection M phi count ra rb rc functionSource functionQ
    eb ec en functionBase t marker marker_name pb pc pn base range :
  raw_collection_template_certificates M t marker ->
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb -> schema_renaming M RepC phi rc ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  numerical_quotation M functionSource eb ec en functionBase t functionQ ->
  quotation_safe M eb ec en functionBase t -> stable_context_support M pb pc pn functionQ ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M pb pc pn marker ->
  quotation_safe M eb ec en base t ->
  skeleton_quotation M replacement_range_skeleton (schema_env3 ra rb rc) eb ec en base t range ->
  contextually_provable M pb pc pn range.
Proof.
  intros HRaw HB RA RB RC GF FQ HF PF HM PM HBase HRange.
  set (names:=cons pb (cons eb (cons t (cons (zeroM M) nil)))).
  set (a:=replacement_name_bound M names).
  assert (Large:forall value,In value names -> coding_lt M value a).
  { intros value HV;exact (replacement_name_bound_above M names value HV). }
  assert (HpbA:coding_lt M pb a) by (apply Large;unfold names;simpl;tauto).
  assert (HebA:coding_lt M eb a) by (apply Large;unfold names;simpl;tauto).
  assert (HtA:coding_lt M t a) by (apply Large;unfold names;simpl;tauto).
  assert (H0A:coding_lt M (zeroM M) a) by (apply Large;unfold names;simpl;tauto).
  assert (HA:quotation_safe M eb ec en a t).
  { split;[exact HtA|exact (environment_below_above_code M eb ec en a HebA H0A)]. }
  destruct (environment_cons_total M eb ec en a) as [ab [ac [an HCons]]].
  assert (HBranch:quotation_safe M ab ac an (succM M a) t).
  { exact (replacement_safe_cons M eb ec en a ab ac an (succM M a) t
      (quotation_safe_successor M eb ec en a t HA) (coding_lt_succ M a) HCons). }
  destruct (skeleton_quotation_total M replacement_collector_skeleton (schema_env3 ra rb rc)
    ab ac an (succM M a) t) as [collector HCollector].
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1)) (t .: a .: fun _=>zeroM M)) as [da GD].
  apply (proj1 (ns_atom_expression M _ false (CEvar 0) (CEvar 1) t a da eq_refl eq_refl)) in GD.
  destruct (environment_cons_total M pb pc pn da) as [db [dc [dn HD]]].
  apply (contextual_skeleton_all_arbitrary_introduction M pb pc pn replacement_collector_skeleton
    (schema_env3 ra rb rc) eb ec en ab ac an base (succM M a) t a range collector da db dc dn
    HBase HA HCons HBranch HRange HCollector GD HD (context_fresh_above_code M pb pc pn a HpbA)).
  apply (quoted_replacement_collector_from_raw_collection M phi count ra rb rc functionSource functionQ
    eb ec en functionBase t a marker marker_name db dc dn ab ac an (succM M a) collector da);
    try assumption.
  - exact (stable_context_support_cons M pb pc pn da db dc dn functionQ HD PF).
  - exact (stable_context_support_cons M pb pc pn da db dc dn marker HD PM).
  - apply stable_context_support_member.
    apply (proj2 (context_member_cons M pb pc pn da db dc dn da HD));now left.
Qed.

Print Assumptions quoted_replacement_range_from_raw_collection.
