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
  SourceOrdinalRangeMembers SourceLeastOrdinalWitness SourceOrdinalCollectorShell SourceOrdinalCollectionPlan.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_ordinal_collection_plan M b c n phi total mono output envelope leastDouble count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_output_graph M phi (code_numeral M 1) output ->
  source_oc_collection_plan M phi total mono output envelope leastDouble ->
  source_full_prv M b c n envelope ->source_full_prv M b c n total ->
  source_full_prv M b c n mono ->source_full_prv M b c n leastDouble ->source_full_prv M b c n output.
Proof.
  intros HB HG
    (phiU&ocU&matrixU&profile&profileU&upper&decorated&totalY&totalU&monoY&monoU&
      leastAll&leastY&outputY&coverU&outputBody&upperPoint&upperBody&
      HCU&HOU&HMU&HProfileShift&HPU&HD&HE&HTYShift&HTUShift&HMYShift&HMUShift&HMUCode&
      HPlan&HLeastY&HLeastDouble&HOutputShift&HCovU&HOutputBody&HOutputY&HUpperPoint&HUpperBody&HUpperEx)
    PEnvelope PTotal PMono PLeastDouble.
  pose proof (source_cutoff_shift_bounded M 2 phi phiU count HB HCU) as HBU.
  destruct (context_shift_total M b c n) as (yb0&yc0&HOuterShift).
  destruct (source_full_prv_wellformed M b c n envelope PEnvelope) as (bound&HEnvelopeBound&HCtxBound).
  pose proof (proj1 (source_bounded_accept_unary M SFEx decorated envelope bound
    (or_intror eq_refl) HE) HEnvelopeBound) as HDecoratedBound.
  destruct (environment_cons_total M yb0 yc0 n decorated) as (yb&yc&yn&HConsY).
  assert (HYBound:context_bounded M yb yc yn (succM M bound)).
  { exact (proj2 (context_bounded_cons M yb0 yc0 n decorated yb yc yn _ HConsY)
      (conj HDecoratedBound (context_shift_preserves_bound M b c n yb0 yc0 bound HOuterShift HCtxBound))). }
  assert (PDecorated:source_full_prv M yb yc yn decorated).
  { apply full_source_Ctx;[exists (succM M bound);auto|].
    apply (proj2 (context_member_cons M yb0 yc0 n decorated yb yc yn decorated HConsY)). now left. }
  pose proof (source_full_conjunction_left M yb yc yn profile upper decorated HD PDecorated) as PProfile.
  pose proof (source_full_conjunction_right M yb yc yn profile upper decorated HD PDecorated) as PUpper.
  assert (PTotalY:source_full_prv M yb yc yn totalY).
  { exact (source_full_prv_shift_cons M b c n yb0 yc0 yb yc yn decorated total totalY (succM M bound)
      HOuterShift HConsY HYBound HTYShift PTotal). }
  assert (PMonoY:source_full_prv M yb yc yn monoY).
  { exact (source_full_prv_shift_cons M b c n yb0 yc0 yb yc yn decorated mono monoY (succM M bound)
      HOuterShift HConsY HYBound HMYShift PMono). }
  assert (PLeastY:source_full_prv M yb yc yn leastY).
  { exact (source_full_prv_weaken_bounded M yb0 yc0 n yb yc yn leastY (succM M bound)
      (source_full_all_shift M b c n leastY leastDouble yb0 yc0 HLeastDouble PLeastDouble HOuterShift)
      (SourceLeastOrdinalWitness.source_cons_tail_inclusion M yb0 yc0 n decorated yb yc yn HConsY) HYBound). }
  destruct (source_full_prv_wellformed M yb yc yn upper PUpper) as (ubound&HUpperBound&HYCtx).
  pose proof (proj1 (source_bounded_accept_unary M SFEx upperBody upper ubound
    (or_intror eq_refl) HUpperEx) HUpperBound) as HUpperBodyBound.
  destruct (context_shift_total M yb yc yn) as (tb&tc&HShiftU).
  destruct (environment_cons_total M tb tc yn upperBody) as (ub&uc&un&HConsU).
  assert (HUBound:context_bounded M ub uc un (succM M ubound)).
  { exact (proj2 (context_bounded_cons M tb tc yn upperBody ub uc un _ HConsU)
      (conj HUpperBodyBound (context_shift_preserves_bound M yb yc yn tb tc ubound HShiftU HYCtx))). }
  assert (PUpperBody:source_full_prv M ub uc un upperBody).
  { apply full_source_Ctx;[exists (succM M ubound);auto|].
    apply (proj2 (context_member_cons M tb tc yn upperBody ub uc un upperBody HConsU)). now left. }
  pose proof (source_full_conjunction_left M ub uc un (source_ordinal_predicate_code M)
    upperPoint upperBody HUpperBody PUpperBody) as POrd.
  pose proof (source_full_conjunction_right M ub uc un (source_ordinal_predicate_code M)
    upperPoint upperBody HUpperBody PUpperBody) as PUpperPoint.
  assert (PProfileU:source_full_prv M ub uc un profileU).
  { exact (source_full_prv_shift_cons M yb yc yn tb tc ub uc un upperBody profile profileU
      (succM M ubound) HShiftU HConsU HUBound HProfileShift PProfile). }
  assert (PTotalU:source_full_prv M ub uc un totalU).
  { exact (source_full_prv_shift_cons M yb yc yn tb tc ub uc un upperBody totalY totalU
      (succM M ubound) HShiftU HConsU HUBound HTUShift PTotalY). }
  assert (PMonoU:source_full_prv M ub uc un monoU).
  { exact (source_full_prv_shift_cons M yb yc yn tb tc ub uc un upperBody monoY monoU
      (succM M ubound) HShiftU HConsU HUBound HMUShift PMonoY). }
  assert (PLeastAll:source_full_prv M ub uc un leastAll).
  { exact (source_full_prv_weaken_bounded M tb tc yn ub uc un leastAll (succM M ubound)
      (source_full_all_shift M yb yc yn leastAll leastY tb tc HLeastY PLeastY HShiftU)
      (SourceLeastOrdinalWitness.source_cons_tail_inclusion M tb tc yn upperBody ub uc un HConsU) HUBound). }
  pose proof (source_full_oc_coverage_prepared M ub uc un phiU ocU matrixU (code_numeral M 2)
    totalU leastAll coverU profileU upperPoint monoU (code_numeral M 1) (succM M count)
    HBU HOU HMU HPlan HCovU HPU HUpperPoint HMUCode PTotalU PLeastAll PProfileU PUpperPoint POrd PMonoU) as PCover.
  pose proof (full_source_CI M ub uc un (source_ordinal_predicate_code M) coverU outputBody
    (source_wf_binary M ub uc un SFAnd _ _ outputBody (or_introl eq_refl) HOutputBody
      (source_full_prv_wellformed M ub uc un _ POrd) (source_full_prv_wellformed M ub uc un coverU PCover))
    POrd PCover HOutputBody) as POutputBody.
  pose proof (source_oc_output_bounded M phiU (code_numeral M 2) outputY (succM M count) HBU
    ltac:(apply (proj2 (coding_lt_succ_cancel M (code_numeral M 1) (succM M (succM M count))));
      apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M count)));apply coding_zero_lt_succ)
    (ex_intro _ coverU (ex_intro _ outputBody (conj HCovU (conj HOutputBody HOutputY))))) as HOutputYBound.
  destruct (numerical_renaming_total M outputY (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (outputU&HOutputYShift).
  pose proof (source_full_exists_map M yb yc yn upperBody outputBody upper outputY tb tc ub uc un outputU
    (source_oc_sequent_two_bounds M yb yc yn outputY (succM M (succM M count)) (succM M bound)
      HOutputYBound HYBound) HUpperEx HOutputY HShiftU HConsU HOutputYShift PUpper POutputBody) as POutputY.
  apply (full_source_ExE M b c n decorated envelope output outputY yb0 yc0 yb yc yn).
  - apply (source_oc_sequent_two_bounds M b c n output (succM M count) bound);[|exact HCtxBound].
    exact (source_oc_output_bounded M phi (code_numeral M 1) output count HB
      ltac:(apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M count)));apply coding_zero_lt_succ) HG).
  - exact PEnvelope.
  - exact POutputY.
  - exact HE.
  - exact HOuterShift.
  - exact HConsY.
  - exact HOutputShift.
Qed.

Print Assumptions source_full_ordinal_collection_plan.
