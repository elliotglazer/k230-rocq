(** The actual collector and upper-ordinal existential shells for uniform
    ordinal collection. Every varying matrix is an internal source code. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents
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
  SourceOrdinalRangeMembers SourceLeastOrdinalWitness.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Lemma source_oc_sequent_two_bounds M b c n f k l :source_bounded M f k ->context_bounded M b c n l ->
  source_sequent_wf M b c n f.
Proof.
  intros HF HC. exists (addM M k l). split.
  - exact (source_bounded_monotone M f k (addM M k l) HF (coding_le_add M k l)).
  - apply (context_bounded_monotone M b c n l (addM M k l) HC).
    rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.

Lemma source_replacement_profile_canonical_at M matrix profile :
  source_replacement_profile_graph M matrix profile ->
  source_replacement_profile_at_graph M (zeroM M) (code_numeral M 1) matrix profile.
Proof.
  intro HP. unfold source_replacement_profile_graph,E_source_replacement_profile in HP.
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HP) as (point&HPoint&HAll).
  destruct (code_relation_total M (E_sf_mem 0 1) (fun _=>matrix)) as (left&HL).
  destruct (code_relation_total M (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3) (CEvar 0))) (fun _=>matrix))
    as (ex&HExCode).
  destruct (SourceOrdinalRangeMembers.source_range_iff_split M _ _ _ left ex point HL HExCode HPoint)
    as (forward&reverse&HF&HR&HPt).
  destruct (schema_expression_quantifier_split M _ SFEx _ ex HExCode) as (body&HBodyCode&HEx).
  destruct (schema_expression_split M _ SFAnd _ _ body HBodyCode) as (input&matrix'&HI&HM&HBody).
  change (matrix'=matrix) in HM. subst matrix'.
  apply (source_replacement_profile_at_join M (zeroM M) (code_numeral M 1) matrix profile left input body ex point).
  - exact (proj1 (schema_expression_graph M (fun _=>matrix) SFMember (CEconst 0) (CEconst 1)
      (zeroM M) (code_numeral M 1) left eq_refl eq_refl) HL).
  - exact (proj1 (schema_expression_graph M (fun _=>matrix) SFMember (CEconst 0) (CEconst 3)
      (zeroM M) (code_numeral M 3) input eq_refl eq_refl) HI).
  - exact HBody.
  - exact HEx.
  - unfold replacement_profile_point_template,source_prop_expression. functionality_graph.
  - exact HAll.
Qed.

Theorem source_zfr_ordinal_collection M phi total mono output count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_initial_totality_graph M phi total ->source_oc_initial_monotonicity_graph M phi mono ->
  source_oc_output_graph M phi (code_numeral M 1) output ->
  source_zfr_provable M total ->source_zfr_provable M mono ->source_zfr_provable M output.
Proof.
  intros HB HT0 HM0 HG PT0 PM0.
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
  assert (Premises:forall f,In f [envelope;total;mono;leastDouble] ->
    source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f [<-|[<-|[<-|[<-|[]]]]];apply (proj2 (source_zfr_descriptor_provable M _));assumption. }
  destruct (source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises)
    as (b&c&n&HContext&P).
  pose proof (P envelope (or_introl eq_refl)) as PEnvelope.
  pose proof (P total (or_intror (or_introl eq_refl))) as PTotal.
  pose proof (P mono (or_intror (or_intror (or_introl eq_refl)))) as PMono.
  pose proof (P leastDouble (or_intror (or_intror (or_intror (or_introl eq_refl))))) as PLeastDouble.
  pose proof (source_closed_context_shift_self M b c n (proj1 HContext)) as HClosedShift.
  destruct (source_full_prv_wellformed M b c n envelope PEnvelope) as (bound&HEnvelopeBound&HCtxBound).
  pose proof (proj1 (source_bounded_accept_unary M SFEx decorated envelope bound
    (or_intror eq_refl) HE) HEnvelopeBound) as HDecoratedBound.
  destruct (environment_cons_total M b c n decorated) as (yb&yc&yn&HConsY).
  assert (HYBound:context_bounded M yb yc yn (succM M bound)).
  { exact (proj2 (context_bounded_cons M b c n decorated yb yc yn _ HConsY)
      (conj HDecoratedBound (context_bounded_monotone M b c n (zeroM M) (succM M bound)
        (proj1 HContext) (coding_zero_lt_succ M (succM M bound))))). }
  assert (PDecorated:source_full_prv M yb yc yn decorated).
  { apply full_source_Ctx;[exists (succM M bound);auto|].
    apply (proj2 (context_member_cons M b c n decorated yb yc yn decorated HConsY)). now left. }
  pose proof (source_full_conjunction_left M yb yc yn profile upper decorated HD PDecorated) as PProfile.
  pose proof (source_full_conjunction_right M yb yc yn profile upper decorated HD PDecorated) as PUpper.
  assert (PTotalY:source_full_prv M yb yc yn totalY).
  { exact (source_full_prv_shift_cons M b c n b c yb yc yn decorated total totalY (succM M bound)
      HClosedShift HConsY HYBound HTYShift PTotal). }
  assert (PMonoY:source_full_prv M yb yc yn monoY).
  { exact (source_full_prv_shift_cons M b c n b c yb yc yn decorated mono monoY (succM M bound)
      HClosedShift HConsY HYBound HMYShift PMono). }
  assert (PLeastY:source_full_prv M yb yc yn leastY).
  { exact (source_full_prv_weaken_bounded M b c n yb yc yn leastY (succM M bound)
      (source_full_all_shift M b c n leastY leastDouble b c HLeastDouble PLeastDouble HClosedShift)
      (SourceLeastOrdinalWitness.source_cons_tail_inclusion M b c n decorated yb yc yn HConsY) HYBound). }
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
  exists b,c,n. split;[exact (proj1 (source_zfr_descriptor_context M b c n) HContext)|].
  apply (full_source_ExE M b c n decorated envelope output outputY b c yb yc yn).
  - exists (succM M count). split.
    + exact (source_oc_output_bounded M phi (code_numeral M 1) output count HB
        ltac:(apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M count)));apply coding_zero_lt_succ) HG).
    + exact (context_bounded_monotone M b c n (zeroM M) (succM M count) (proj1 HContext)
        (coding_zero_lt_succ M (succM M count))).
  - exact PEnvelope.
  - exact POutputY.
  - exact HE.
  - exact HClosedShift.
  - exact HConsY.
  - exact HOutputShift.
Qed.

Print Assumptions source_zfr_ordinal_collection.
