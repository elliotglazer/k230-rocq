(** Close the input guard and universal quantifier of actual ordinal
    coverage. The least-witness existential is eliminated internally. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSubstitution
  NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceInstantiationConstructors
  SourceFiniteCutoffShift SourceRoleReopening SourceRoleInstanceShift SchemaRenamingDescriptors
  SourceOrdinalPredicate SourceDomainInstances SourceOrdinalCollectionRecipe SourceOrdinalCollectionCutoff
  SourceReplacementMemberAt SourceOrdinalUpperMembers SourceOrdinalMonotoneUse SourceOrdinalMonotonicityShift
  SourceOrdinalProfileAdvance SourceProofShiftCons SourceOrdinalLeastRangeElimination
  SourceDerivedRules SourceUniversalPropositional SourceQfFunctionality SourceProofWeakening SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_oc_coverage_all M b c n phi phiV phiD oc ocV ocD matrix
    leastbody least inputbody exOrd input totalpoint total leastImp leastAll
    result coverpoint cover profile upper ordU mono sb sc s x u count :
  source_bounded M phi (succM M (succM M count)) ->
  source_cutoff_shift M 2 phi phiV ->source_cutoff_shift M 2 phiV phiD ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  source_cutoff_shift M 2 oc ocV ->source_cutoff_shift M 2 ocV ocD ->schema_renaming M RepC oc matrix ->
  numerical_renaming M ocD (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody ->sf_relation M SFEx leastbody (zeroM M) least ->
  sf_relation M SFAnd (source_ordinal_predicate_code M) phiD inputbody ->
  sf_relation M SFEx inputbody (zeroM M) exOrd ->sf_relation M SFMember (zeroM M) (succM M x) input ->
  sf_relation M SFImpl input exOrd totalpoint ->sf_relation M SFAll totalpoint (zeroM M) total ->
  sf_relation M SFImpl exOrd least leastImp ->sf_relation M SFAll leastImp (zeroM M) leastAll ->
  source_role_reopening M (zeroM M) (succM M u) sb sc ->
  numerical_substitution M phiV sb sc (code_numeral M 2) (code_numeral M 2) result ->
  sf_relation M SFImpl input result coverpoint ->sf_relation M SFAll coverpoint (zeroM M) cover ->
  source_replacement_profile_at_graph M s x matrix profile ->source_oc_upper_point_graph M s u upper ->
  numerical_instantiation M (source_ordinal_predicate_code M) u ordU ->
  source_oc_monotonicity_graph M phi mono ->
  source_full_prv M b c n total ->source_full_prv M b c n leastAll ->
  source_full_prv M b c n profile ->source_full_prv M b c n upper ->
  source_full_prv M b c n ordU ->source_full_prv M b c n mono ->source_full_prv M b c n cover.
Proof.
  intros HB HCv HCd HO HOv HOd HM HSwap HEx HInputBody HInputEx HI HTp HT HLp HL
    HRole HResult HCp HC HP HU HOrd HMono PT PL PP PU PO PM.
  pose proof (source_cutoff_shift_bounded M 2 phi phiV count HB HCv) as HBv.
  destruct (source_oc_profile_advance M phi oc matrix profile s x count HB HO HM HP)
    as (phiV'&ocV'&matrixV&profileV&HCv'&HOv'&HOV&HMV&HPV&HProfileShift).
  pose proof (source_cutoff_shift_functional M 2 phi phiV' phiV HCv' HCv) as E. subst phiV'.
  pose proof (source_cutoff_shift_functional M 2 oc ocV' ocV HOv' HOv) as E. subst ocV'.
  destruct (numerical_renaming_total M upper (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (upperV&HUpperShift).
  pose proof (source_oc_upper_point_shift M s u upper upperV HU HUpperShift) as HUV.
  destruct (numerical_renaming_total M ordU (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (ordV&HOrdShift).
  pose proof (source_domain_instance_shift M _ u ordU ordV (source_ordinal_predicate_bounded M)
    HOrd HOrdShift) as HOrdV.
  destruct (numerical_renaming_total M mono (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (monoV&HMonoShift).
  pose proof (source_oc_monotonicity_shift M phi phiV mono monoV (succM M (succM M count))
    HB HMono HCv HMonoShift) as HMonoV.
  destruct (source_full_prv_wellformed M b c n total PT) as (bound&HBound&HCtx).
  pose proof (proj1 (source_bounded_accept_unary M SFAll totalpoint total bound
    (or_introl eq_refl) HT) HBound) as HPointBound.
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl input exOrd totalpoint
    (succM M bound) (or_intror (or_intror eq_refl)) HTp) HPointBound)) as HInputBound.
  destruct (context_shift_total M b c n) as (cb&cc&HShift).
  destruct (environment_cons_total M cb cc n input) as (eb&ec&en&HCons).
  assert (HCtxV:context_bounded M cb cc n (succM M bound)).
  { exact (context_shift_preserves_bound M b c n cb cc bound HShift HCtx). }
  assert (HBranch:context_bounded M eb ec en (succM M bound)).
  { exact (proj2 (context_bounded_cons M cb cc n input eb ec en _ HCons) (conj HInputBound HCtxV)). }
  assert (PI:source_full_prv M eb ec en input).
  { apply full_source_Ctx;[exists (succM M bound);auto|].
    apply (proj2 (context_member_cons M cb cc n input eb ec en input HCons)). now left. }
  assert (PTPoint:source_full_prv M eb ec en totalpoint).
  { exact (SourceProofWeakening.source_full_prv_weaken_bounded M cb cc n eb ec en totalpoint
      (succM M bound) (source_full_all_shift M b c n totalpoint total cb cc HT PT HShift)
      (SourceLeastOrdinalWitness.source_cons_tail_inclusion M cb cc n input eb ec en HCons) HBranch). }
  assert (PLeastImp:source_full_prv M eb ec en leastImp).
  { exact (SourceProofWeakening.source_full_prv_weaken_bounded M cb cc n eb ec en leastImp
      (succM M bound) (source_full_all_shift M b c n leastImp leastAll cb cc HL PL HShift)
      (SourceLeastOrdinalWitness.source_cons_tail_inclusion M cb cc n input eb ec en HCons) HBranch). }
  pose proof (source_full_modus_ponens M eb ec en input exOrd totalpoint HTp PTPoint PI) as PInputEx.
  pose proof (source_full_modus_ponens M eb ec en exOrd least leastImp HLp PLeastImp PInputEx) as PLeast.
  assert (PPV:source_full_prv M eb ec en profileV).
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en input profile profileV
      (succM M bound) HShift HCons HBranch HProfileShift PP). }
  assert (PUV:source_full_prv M eb ec en upperV).
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en input upper upperV
      (succM M bound) HShift HCons HBranch HUpperShift PU). }
  assert (POV:source_full_prv M eb ec en ordV).
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en input ordU ordV
      (succM M bound) HShift HCons HBranch HOrdShift PO). }
  assert (PMV:source_full_prv M eb ec en monoV).
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en input mono monoV
      (succM M bound) HShift HCons HBranch HMonoShift PM). }
  pose proof (source_full_oc_least_range_elimination M eb ec en phiV phiD ocV ocD matrixV
    leastbody least profileV upperV input ordV monoV result sb sc
    (succM M s) (succM M x) (succM M u) (succM M count)
    HBv HCd HOV HMV HOd HSwap HEx HPV HUV HI HOrdV HMonoV HRole HResult
    PLeast PPV PUV PI POV PMV) as PResult.
  set (resbound:=succM M (addM M (succM M (succM M (succM M count))) (succM M u))).
  assert (HResultBound:source_bounded M result resbound).
  { apply (source_role_instance_bounded M phiV (zeroM M) (succM M u) sb sc result
      (succM M (succM M (succM M count))) resbound HBv HRole HResult).
    - unfold resbound. apply coding_lt_succ_cases. left. apply coding_le_add.
    - unfold resbound. apply coding_zero_lt_succ.
    - unfold resbound. rewrite Arithmetic.add_comm. apply coding_le_add. }
  set (outbound:=addM M (succM M bound) resbound).
  assert (HCPoint:source_bounded M coverpoint outbound).
  { apply (proj2 (source_bounded_accept_binary M SFImpl input result coverpoint outbound
      (or_intror (or_intror eq_refl)) HCp)). split.
    - exact (source_bounded_monotone M input (succM M bound) outbound HInputBound
        (coding_le_add M (succM M bound) resbound)).
    - apply (source_bounded_monotone M result resbound outbound HResultBound).
      unfold outbound. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (HOutBound:source_bounded M cover outbound).
  { apply (proj2 (source_bounded_accept_unary M SFAll coverpoint cover outbound (or_introl eq_refl) HC)).
    apply (source_bounded_monotone M coverpoint outbound (succM M outbound) HCPoint).
    apply coding_lt_succ_cases. left. apply coding_lt_succ. }
  assert (HCtxOut:context_bounded M b c n outbound).
  { apply (context_bounded_monotone M b c n bound outbound HCtx).
    unfold outbound. apply coding_lt_succ_cases. left.
    rewrite Arithmetic.add_succ. apply coding_le_add. }
  apply (full_source_AllI M b c n coverpoint cover cb cc (ex_intro _ outbound (conj HOutBound HCtxOut)));
    [|exact HShift|exact HC].
  apply (full_source_II M cb cc n input result coverpoint eb ec en);[|exact PResult|exact HCons|exact HCp].
  exists (succM M outbound). split.
  - exact (source_bounded_monotone M coverpoint outbound (succM M outbound) HCPoint
      ltac:(apply coding_lt_succ_cases;left;apply coding_lt_succ)).
  - exact (context_shift_preserves_bound M b c n cb cc outbound HShift HCtxOut).
Qed.

Print Assumptions source_full_oc_coverage_all.
