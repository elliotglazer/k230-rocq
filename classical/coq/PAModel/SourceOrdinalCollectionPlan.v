(** The actual collector and upper-ordinal existential shells for uniform
    ordinal collection. Every varying matrix is an internal source code. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SchemaRenamingDescriptors SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull
  SourceQuantifierRules SourceInstantiationConstructors SourceConjunctionRules SourceProofWeakening
  SourceClosedContextShift SourceProofShiftCons SourceExistentialMap SourceUniversalPropositional
  SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceFiniteProofContexts
  SourceZFRProvability SourceFiniteCutoffShift SourceOrdinalPredicate SourceOrdinalCollectionRecipe
  SourceOrdinalCollector SourceOrdinalEnvelope SourceOrdinalUnion SourceOrdinalUpperMembers
  SourceReplacementCollector SourceReplacementMemberAt SourceReplacementProfileShift
  SourceOrdinalTotality SourceOrdinalInitialTotality SourceOrdinalMonotoneUse SourceOrdinalMonotonicityShift
  SourceOrdinalInitialMonotonicity SourceOrdinalProfileAdvance SourceOrdinalCoverageSyntax SourceOrdinalCoveragePlan
  SourcePropositionalRebase SourceWFSeparationConstructor SourceFunctionalityShells SourcePropositionalTemplates
  SourceOrdinalRangeMembers SourceLeastOrdinalWitness SourceOrdinalCollectorShell.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_oc_collection_plan M phi total mono output envelope leastDouble :=
  exists phiU ocU matrixU profile profileU upper decorated totalY totalU monoY monoU
    leastAll leastY outputY coverU outputBody upperPoint upperBody,
    source_cutoff_shift M 2 phi phiU /\
    source_oc_form M (source_ordinal_predicate_code M) phiU ocU /\schema_renaming M RepC ocU matrixU /\
    source_formula_shift M profile profileU /\
    source_replacement_profile_at_graph M (code_numeral M 1) (code_numeral M 2) matrixU profileU /\
    sf_relation M SFAnd profile upper decorated /\sf_relation M SFEx decorated (zeroM M) envelope /\
    source_formula_shift M total totalY /\source_formula_shift M totalY totalU /\
    source_formula_shift M mono monoY /\source_formula_shift M monoY monoU /\
    source_oc_monotonicity_graph M phiU monoU /\
    source_oc_coverage_plan M phiU ocU (code_numeral M 2) totalU leastAll /\
    sf_relation M SFAll leastAll (zeroM M) leastY /\sf_relation M SFAll leastY (zeroM M) leastDouble /\
    source_formula_shift M output outputY /\source_oc_cover_graph M phiU (code_numeral M 2) coverU /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) coverU outputBody /\
    sf_relation M SFEx outputBody (zeroM M) outputY /\
    source_oc_upper_point_graph M (code_numeral M 1) (zeroM M) upperPoint /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) upperPoint upperBody /\
    sf_relation M SFEx upperBody (zeroM M) upper.

Theorem source_oc_collection_plan_total M phi total mono output count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_initial_totality_graph M phi total ->source_oc_initial_monotonicity_graph M phi mono ->
  source_oc_output_graph M phi (code_numeral M 1) output ->
  exists envelope leastDouble,source_oc_collection_plan M phi total mono output envelope leastDouble /\
    source_zfr_provable M envelope /\source_zfr_provable M leastDouble.
Proof.
  intros HB HT0 HM0 HG.
  destruct (source_oc_form_total M (source_ordinal_predicate_code M) phi) as (oc&HO).
  destruct (source_zfr_oc_upper_envelope_total M phi oc count HB HO)
    as (matrix&profile&collector&upper&decorated&envelope&HM&HP&HC&PC&HU&HD&HE&PE).
  pose proof (source_replacement_profile_canonical_at M matrix profile HP) as HProfile.
  destruct (source_oc_profile_advance M phi oc matrix profile (zeroM M) (code_numeral M 1) count
    HB HO HM HProfile) as (phiU&ocU&matrixU&profileU&HCU&HCO&HOU&HMU&HPU&HProfileShift).
  pose proof (source_cutoff_shift_bounded M 2 phi phiU count HB HCU) as HBU.
  destruct (numerical_renaming_total M total (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (totalY&HTYShift).
  pose proof (source_oc_initial_totality_shift M phi total totalY HT0 HTYShift) as HTY.
  destruct (numerical_renaming_total M totalY (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (totalU&HTUShift).
  pose proof (source_oc_totality_shift M phi phiU (code_numeral M 1) totalY totalU HTY HCU HTUShift) as HTU.
  destruct (numerical_renaming_total M mono (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (monoY&HMYShift).
  pose proof (source_oc_initial_monotonicity_shift M phi mono monoY (succM M (succM M count))
    HB HM0 HMYShift) as HMY.
  destruct (numerical_renaming_total M monoY (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (monoU&HMUShift).
  pose proof (source_oc_monotonicity_shift M phi phiU monoY monoU (succM M (succM M count))
    HB HMY HCU HMUShift) as HMUCode.
  destruct (source_oc_coverage_plan_total M phiU ocU (code_numeral M 2) totalU (succM M count)
    HBU HOU HTU) as (leastAll&HPlan&PLeast).
  destruct (sf_relation_total M SFAll leastAll (zeroM M)) as (leastY&HLeastY).
  destruct (sf_relation_total M SFAll leastY (zeroM M)) as (leastDouble&HLeastDouble).
  assert (PDouble:source_zfr_provable M leastDouble).
  { apply (proj1 (source_zfr_descriptor_provable M leastDouble)).
    apply (source_descriptor_provable_all M ZFRSourceDescriptor leastY leastDouble);[|exact HLeastDouble].
    exact (source_descriptor_provable_all M ZFRSourceDescriptor leastAll leastY
      (proj2 (source_zfr_descriptor_provable M leastAll) PLeast) HLeastY). }
  destruct (numerical_renaming_total M output (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (outputY&HOutputShift).
  destruct (source_oc_output_shift M phi phiU output outputY count HB HCU HG HOutputShift)
    as (coverU&outputBody&HCovU&HOutputBody&HOutputY).
  destruct (source_ordinal_upper_shell M upper HU) as (upperPoint&upperBody&HUpperPoint&HUpperBody&HUpperEx).
  exists envelope,leastDouble. split;[|auto].
  exists phiU,ocU,matrixU,profile,profileU,upper,decorated,totalY,totalU,monoY,monoU,
    leastAll,leastY,outputY,coverU,outputBody,upperPoint,upperBody.
  repeat split;assumption.
Qed.

Print Assumptions source_oc_collection_plan_total.
