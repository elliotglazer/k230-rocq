(** The exact pointwise source Replacement body is provable from a raw
    Collection profile; all quotation details are discharged here. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeExpressions NumericalProofs NumericalQuotation
  NumericalEnvironments QuotationHygiene QuotationPayloads QuotationSchemaSkeleton
  SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors SourceBounded
  StableContextSupport SupportedQuotientEnvironments RawQuotientAtomCongruence
  RawCollectionProfile RawClauseAlpha ReplacementMatrixQuotation MatrixClauseRenaming
  RawProfilePointwiseRange ReplacementPointwiseSkeleton QuotedInstantiationRules QuotedSameBaseRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem quoted_replacement_pointwise_from_profile M phi count ra rb rc functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name pb pc pn
    ab ac an cb cc cn yb yc yn y base result dy :
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
  environment_cons M cb cc cn y yb yc yn ->
  quotation_safe M eb ec en base t -> coding_lt M a base -> coding_lt M c base -> coding_lt M y base ->
  membership_graph M t y dy -> stable_context_support M pb pc pn dy ->
  skeleton_quotation M replacement_pointwise_skeleton (schema_env3 ra rb rc) yb yc yn base t result ->
  stable_context_support M pb pc pn result.
Proof.
  intros HB RA RB RC GF FQ HF PF HM PM NU0 NV0 HUV HP Q0 GP PP HA HC HY
    HBase HAB HCB HYB GD PD HR.
  destruct (replacement_pointwise_skeleton_data M phi (succM M (succM M count)) ra rb rc
    eb ec en a c y ab ac an cb cc cn yb yc yn base t result HB RC HA HC HY HR)
    as (left & image & forward & backward & GL & GI & GFwd & GBwd & GAnd).
  apply (raw_profile_pointwise_range_equivalence M phi count ra rb functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name pb pc pn
    base y (succM M base) (succM M base) image base left dy forward backward result);
    try assumption.
  - repeat split.
    + exact (coding_zero_lt_succ M base).
    + exact (coding_lt_trans M t base (succM M base) (proj1 HBase) (coding_lt_succ M base)).
    + exact (coding_lt_succ M base).
    + exact (coding_lt_trans M a base (succM M base) HAB (coding_lt_succ M base)).
  - exact (quotation_safe_successor M eb ec en base t HBase).
  - exact (coding_lt_succ M base).
  - exact (coding_lt_trans M y base (succM M base) HYB (coding_lt_succ M base)).
  - repeat split;try assumption.
    + exact (SubstitutionEnvironmentTotal.environment_below_zero M eb ec en base (proj2 HBase)).
    + exact (proj1 HBase).
Qed.

Print Assumptions quoted_replacement_pointwise_from_profile.





