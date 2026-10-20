(** Guarded universal output quantification of the proved range relation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeExpressions NumericalProofs NumericalQuotation
  NumericalEnvironments NumericalContexts ContextualProofs StableContextSupport NamedLeibnizSteps
  QuotationHygiene QuotationPayloads QuotationSchemaSkeleton QuotedSameBaseRules
  SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors SourceBounded
  SupportedQuotientEnvironments RawQuotientAtomCongruence RawCollectionProfile RawClauseAlpha
  ReplacementMatrixQuotation ReplacementMatrixCongruence MatrixClauseRenaming
  ReplacementFreshAllocation ContextFreshBounds ReplacementPointwiseSkeleton
  QuotedReplacementPointwise ArbitraryWitnessIntroduction.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma replacement_safe_cons M eb ec en value db dc dn base t :
  quotation_safe M eb ec en base t -> coding_lt M value base ->
  environment_cons M eb ec en value db dc dn -> quotation_safe M db dc dn base t.
Proof.
  intros HS HV HC;split;[exact (proj1 HS)|].
  exact (replacement_environment_push_below M eb ec en value db dc dn base (proj2 HS) HV HC).
Qed.

Theorem quoted_replacement_output_from_profile M phi count ra rb rc functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name pb pc pn
    ab ac an cb cc cn base allout :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb -> schema_renaming M RepC phi rc ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  numerical_quotation M functionSource eb ec en functionBase t functionQ ->
  quotation_safe M eb ec en functionBase t -> stable_context_support M pb pc pn functionQ ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M pb pc pn marker ->
  raw_clause_usable_name M eb ec en t a c profileBase u0 ->
  raw_clause_usable_name M eb ec en t a c profileBase v0 -> u0<>v0 ->
  quotation_safe M eb ec en profileBase t ->
  binary_matrix_quotation M phi eb ec en u0 v0 profileBase t theta0 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  stable_context_support M pb pc pn profile ->
  environment_cons M eb ec en a ab ac an -> environment_cons M ab ac an c cb cc cn ->
  quotation_safe M cb cc cn base t ->
  skeleton_quotation M replacement_output_skeleton (schema_env3 ra rb rc) cb cc cn base t allout ->
  contextually_provable M pb pc pn allout.
Proof.
  intros HB RA RB RC GF FQ HF PF HM PM NU0 NV0 HUV HP Q0 GP PP HA HC HBase HAll.
  set (names:=cons pb (cons eb (cons a (cons c (cons t (cons (zeroM M) nil)))))).
  set (y:=replacement_name_bound M names).
  assert (Large:forall value,In value names -> coding_lt M value y).
  { intros value HV;exact (replacement_name_bound_above M names value HV). }
  assert (HpbY:coding_lt M pb y) by (apply Large;unfold names;simpl;tauto).
  assert (HebY:coding_lt M eb y) by (apply Large;unfold names;simpl;tauto).
  assert (HaY:coding_lt M a y) by (apply Large;unfold names;simpl;tauto).
  assert (HcY:coding_lt M c y) by (apply Large;unfold names;simpl;tauto).
  assert (HtY:coding_lt M t y) by (apply Large;unfold names;simpl;tauto).
  assert (H0Y:coding_lt M (zeroM M) y) by (apply Large;unfold names;simpl;tauto).
  assert (HRoot:quotation_safe M eb ec en y t).
  { split;[exact HtY|exact (environment_below_above_code M eb ec en y HebY H0Y)]. }
  assert (HCollection:quotation_safe M cb cc cn y t).
  { exact (replacement_safe_cons M ab ac an c cb cc cn y t
      (replacement_safe_cons M eb ec en a ab ac an y t HRoot HaY HA) HcY HC). }
  destruct (environment_cons_total M cb cc cn y) as [yb [yc [yn HY]]].
  assert (HBranch:quotation_safe M yb yc yn (succM M y) t).
  { exact (replacement_safe_cons M cb cc cn y yb yc yn (succM M y) t
      (quotation_safe_successor M cb cc cn y t HCollection) (coding_lt_succ M y) HY). }
  destruct (skeleton_quotation_total M replacement_pointwise_skeleton (schema_env3 ra rb rc)
    yb yc yn (succM M y) t) as [result HResult].
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1)) (t .: y .: fun _=>zeroM M)) as [dy GD].
  apply (proj1 (ns_atom_expression M _ false (CEvar 0) (CEvar 1) t y dy eq_refl eq_refl)) in GD.
  destruct (environment_cons_total M pb pc pn dy) as [db [dc [dn HD]]].
  apply (contextual_skeleton_all_arbitrary_introduction M pb pc pn replacement_pointwise_skeleton
    (schema_env3 ra rb rc) cb cc cn yb yc yn base (succM M y) t y allout result dy db dc dn
    HBase HCollection HY HBranch HAll HResult GD HD (context_fresh_above_code M pb pc pn y HpbY)).
  apply stable_context_support_here.
  apply (quoted_replacement_pointwise_from_profile M phi count ra rb rc functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name db dc dn
    ab ac an cb cc cn yb yc yn y (succM M y) result dy);try assumption.
  - exact (stable_context_support_cons M pb pc pn dy db dc dn functionQ HD PF).
  - exact (stable_context_support_cons M pb pc pn dy db dc dn marker HD PM).
  - exact (stable_context_support_cons M pb pc pn dy db dc dn profile HD PP).
  - exact (quotation_safe_successor M eb ec en y t HRoot).
  - exact (coding_lt_trans M a y (succM M y) HaY (coding_lt_succ M y)).
  - exact (coding_lt_trans M c y (succM M y) HcY (coding_lt_succ M y)).
  - exact (coding_lt_succ M y).
  - apply stable_context_support_member.
    apply (proj2 (context_member_cons M pb pc pn dy db dc dn dy HD));now left.
Qed.

Print Assumptions replacement_safe_cons.
Print Assumptions quoted_replacement_output_from_profile.

