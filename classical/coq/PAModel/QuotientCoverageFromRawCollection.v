(** Raw coverage plus an actual functional source matrix yields quotient
    membership. The universal raw clause and functionality are separate,
    explicit numerical proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeExpressions
  NumericalProofs NumericalQuotation NumericalContexts NumericalEnvironments
  ContextualProofs ContextualPropositional StableContextSupport SourceBounded
  QuotationHygiene QuotationPayloads QuotientAtomTemplates QuotationFixedSource SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors
  ReplacementMatrixQuotation NamedExistential NamedBinderFresh ContextualWitnessRules
  CollectionWitnessKernels BinaryMatrixWitnessIntroduction ActualCollectionCoverage RawDmemWitness.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem quotient_coverage_from_raw_collection M phi bound ra rb functionSource functionQ
    eb ec en oldbase t c cb cc cn u y z du dy dz inA memZ thetaY thetaZ eq
    source exsource q child target has guard inner coverage allcoverage db dc dn :
  source_bounded M phi bound -> schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  quotation_safe M eb ec en oldbase t -> quotation_safe M eb ec en z t ->
  coding_lt M u z -> coding_lt M y z ->
  numerical_quotation M functionSource eb ec en oldbase t functionQ ->
  binary_matrix_quotation M phi eb ec en u y (succM M z) t thetaY ->
  binary_matrix_quotation M phi eb ec en u z (succM M z) t thetaZ ->
  membership_graph M t u du -> membership_graph M t y dy ->
  raw_dmem_witness_graph M t y c z q dz memZ eq child target ->
  code_relation M (collection_coverage_parameters M dz memZ thetaZ thetaY eq)
    (coverage_input (CEvar 0) (CEvar 1) (CEvar 2)) source ->
  named_exists_graph M z source exsource -> quotation_quantifier M false z t thetaZ has ->
  quotation_binary M SFAnd du inA guard -> implication_graph M has exsource inner ->
  implication_graph M guard inner coverage -> universal_graph M u coverage allcoverage ->
  named_binder_absent M coverage u -> stable_context_support M cb cc cn allcoverage ->
  stable_context_support M cb cc cn functionQ -> stable_context_support M cb cc cn du ->
  stable_context_support M cb cc cn dy -> stable_context_support M cb cc cn inA ->
  stable_context_support M cb cc cn thetaY ->
  context_fresh M cb cc cn z -> environment_cons M cb cc cn source db dc dn ->
  contextually_provable M cb cc cn q.
Proof.
  intros HB HA HBren HSource HOld HSafe HU HY HFunction HThetaY HThetaZ HDU HDY
    HRaw GS HExSource HHas HGuard HInner HCoverage HAll HAbsent PAll
    PFunction PU PY PInA PThetaY HF HC.
  destruct HRaw as [HDZ [HMemZ [HE [HChild [HTarget HExTarget]]]]].
  assert (PHas : contextually_provable M cb cc cn has).
  { exact (contextual_binary_matrix_output_exists M phi eb ec en cb cc cn u z y t
      thetaZ thetaY dy has HSafe HU HY HThetaZ HThetaY HDY HHas
      (stable_context_support_here M cb cc cn dy PY)
      (stable_context_support_here M cb cc cn thetaY PThetaY)). }
  assert (PCoverage : contextually_provable M cb cc cn coverage).
  { exact (contextual_self_all_specialize M cb cc cn u coverage allcoverage HAbsent HAll
      (stable_context_support_here M cb cc cn allcoverage PAll)). }
  assert (PInner : contextually_provable M cb cc cn inner).
  { apply (contextual_mp M cb cc cn guard inner coverage);[|exact PCoverage|exact HCoverage].
    exact (contextual_conjunction_intro M cb cc cn du inA guard
      (stable_context_support_here M cb cc cn du PU)
      (stable_context_support_here M cb cc cn inA PInA) HGuard). }
  assert (PEx : contextually_provable M cb cc cn exsource).
  { exact (contextual_mp M cb cc cn has exsource inner PHas PInner HInner). }
  set (rho:=collection_coverage_parameters M dz memZ thetaZ thetaY eq).
  assert (GChild : code_relation M rho (E_wa (CEvar 0) (CEvar 1)) child).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 0) (CEvar 1)
      dz memZ child eq_refl eq_refl) HChild). }
  assert (GT : code_relation M rho (coverage_output (CEvar 0) (CEvar 1) (CEvar 4)) target).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (E_wa (CEvar 0) (CEvar 1))
      (CEvar 4) child eq target GChild eq_refl) HTarget). }
  assert (HNext : quotation_safe M eb ec en (succM M z) t).
  { split.
    - exact (coding_lt_trans M t z (succM M z) (proj1 HSafe) (coding_lt_succ M z)).
    - intros i v HV. exact (coding_lt_trans M v z (succM M z) ((proj2 HSafe) i v HV) (coding_lt_succ M z)). }
  exact (actual_collection_coverage_witness M phi bound ra rb functionSource functionQ
    eb ec en oldbase (succM M z) t cb cc cn u y z du dy dz memZ thetaY thetaZ eq
    source target exsource q db dc dn HB HA HBren HSource HOld HNext
    (coding_lt_trans M u z (succM M z) HU (coding_lt_succ M z))
    (coding_lt_trans M y z (succM M z) HY (coding_lt_succ M z)) (coding_lt_succ M z)
    HFunction HThetaY HThetaZ HE HDU HDY HDZ PFunction PU PY PThetaY GS GT HF HExSource HExTarget HC PEx).
Qed.

Print Assumptions quotient_coverage_from_raw_collection.
