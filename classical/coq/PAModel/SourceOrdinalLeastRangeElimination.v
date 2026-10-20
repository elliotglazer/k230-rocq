(** Eliminate the actual least-witness existential using the actual range
    profile, ordinal upper profile and quantified monotonicity proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalSourceFull
  SourceQuantifierRules SourceInstantiationConstructors SchemaRenamingDescriptors
  SourceOrdinalPredicate SourceDomainInstances SourceOrdinalCollectionRecipe SourceOrdinalCollectionCutoff
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceRoleReopening SourceRoleInstanceShift
  SourceReplacementMemberAt SourceReplacementProfileShift SourceOrdinalWitnessUpper SourceOrdinalWitnessRange
  SourceOrdinalUpperMembers SourceOrdinalMonotoneUse SourceProofShiftCons SourceLeastOrdinalWitness
  SourceOrdinalMonotonicityShift.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_oc_least_range_elimination M b c n phi phi' oc oc' matrix
    leastbody least profile upper input ordU mono result sb sc s x u count :
  source_bounded M phi (succM M (succM M count)) ->source_cutoff_shift M 2 phi phi' ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->schema_renaming M RepC oc matrix ->
  source_cutoff_shift M 2 oc oc' ->
  numerical_renaming M oc' (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody ->sf_relation M SFEx leastbody (zeroM M) least ->
  source_replacement_profile_at_graph M s x matrix profile ->source_oc_upper_point_graph M s u upper ->
  sf_relation M SFMember (zeroM M) x input ->
  numerical_instantiation M (source_ordinal_predicate_code M) u ordU ->
  source_oc_monotonicity_graph M phi mono ->
  source_role_reopening M (zeroM M) u sb sc ->
  numerical_substitution M phi sb sc (code_numeral M 2) (code_numeral M 2) result ->
  source_full_prv M b c n least ->source_full_prv M b c n profile ->source_full_prv M b c n upper ->
  source_full_prv M b c n input ->source_full_prv M b c n ordU ->source_full_prv M b c n mono ->
  source_full_prv M b c n result.
Proof.
  intros HB HCut HO HM HCutOC HSwap HEx HP HU HI HOrd HMonoOriginal HRole HResult
    PLeast PP PU PI POrd PM.
  destruct (numerical_renaming_total M mono (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (mono'&HMonoShift).
  pose proof (source_oc_monotonicity_shift M phi phi' mono mono' (succM M (succM M count))
    HB HMonoOriginal HCut HMonoShift) as HMono.
  pose proof (source_cutoff_shift_bounded M 2 phi phi' count HB HCut) as HB'.
  pose proof (source_oc_form_cutoff_two M phi phi' oc oc' (succM M (succM M count))
    HB HO HCut HCutOC) as HO'.
  pose proof (source_oc_form_bounded M _ phi oc count (source_ordinal_predicate_bounded M) HB HO) as HOCBound.
  destruct (renaming_lift_total M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (ab&ac&an&HL1).
  destruct (renaming_lift_total M ab ac an (code_numeral M 1)) as (rb&rc&rn&HL2).
  destruct (numerical_renaming_total M matrix rb rc rn (code_numeral M 1)) as (matrix'&HRM).
  pose proof (source_repc_cutoff_two_shift M oc matrix oc' matrix' (succM M (succM M count))
    ab ac an rb rc rn HOCBound HM HCutOC HL1 HL2 HRM) as HM'.
  destruct (code_relation_total M E_replacement_profile_at
    (replacement_profile_at_environment (succM M s) (succM M x) matrix')) as (profile'&HP').
  pose proof (source_replacement_profile_shift M s x matrix profile matrix' profile'
    ab ac an rb rc rn HP HL1 HL2 HRM HP') as HProfileShift.
  destruct (numerical_renaming_total M upper (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (upper'&HUpperShift).
  pose proof (source_oc_upper_point_shift M s u upper upper' HU HUpperShift) as HU'.
  destruct (sf_relation_total M SFMember (code_numeral M 1) (succM M x)) as (input'&HI').
  assert (HInputShift:source_formula_shift M input input').
  { apply (proj2 (numerical_renaming_member M (zeroM M) x input _ _ _ _ input' HI)).
    exists (code_numeral M 1),(succM M x). split;[apply SourceFilteredProfileShift.source_shift_map_lookup|].
    split;[apply SourceFilteredProfileShift.source_shift_map_lookup|exact HI']. }
  destruct (numerical_renaming_total M ordU (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (ordU'&HOrdShift).
  pose proof (source_domain_instance_shift M _ u ordU ordU' (source_ordinal_predicate_bounded M)
    HOrd HOrdShift) as HOrd'.
  destruct (numerical_renaming_total M result (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (result'&HResultShift).
  destruct (source_role_reopening_total M (code_numeral M 1) (succM M u)) as (tb&tc&HRole').
  pose proof (source_role_instance_shift M phi phi' (zeroM M) u sb sc result result' tb tc
    (succM M (succM M count)) HB HCut HRole HResult HResultShift HRole') as HResult'.
  destruct (source_full_prv_wellformed M b c n least PLeast) as (bound&HLeastBound&HCtx).
  pose proof (proj1 (source_bounded_accept_unary M SFEx leastbody least bound
    (or_intror eq_refl) HEx) HLeastBound) as HBodyBound.
  destruct (context_shift_total M b c n) as (cb&cc&HCtxShift).
  destruct (environment_cons_total M cb cc n leastbody) as (eb&ec&en&HCons).
  assert (HBranch:context_bounded M eb ec en (succM M bound)).
  { exact (proj2 (context_bounded_cons M cb cc n leastbody eb ec en _ HCons)
      (conj HBodyBound (context_shift_preserves_bound M b c n cb cc bound HCtxShift HCtx))). }
  assert (PW:source_full_prv M eb ec en leastbody).
  { apply full_source_Ctx;[exists (succM M bound);auto|].
    apply (proj2 (context_member_cons M cb cc n leastbody eb ec en leastbody HCons)). now left. }
  assert (PP':source_full_prv M eb ec en profile').
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en leastbody profile profile' (succM M bound)
      HCtxShift HCons HBranch HProfileShift PP). }
  assert (PU':source_full_prv M eb ec en upper').
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en leastbody upper upper' (succM M bound)
      HCtxShift HCons HBranch HUpperShift PU). }
  assert (PI':source_full_prv M eb ec en input').
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en leastbody input input' (succM M bound)
      HCtxShift HCons HBranch HInputShift PI). }
  assert (POrd':source_full_prv M eb ec en ordU').
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en leastbody ordU ordU' (succM M bound)
      HCtxShift HCons HBranch HOrdShift POrd). }
  assert (PM':source_full_prv M eb ec en mono').
  { exact (source_full_prv_shift_cons M b c n cb cc eb ec en leastbody mono mono' (succM M bound)
      HCtxShift HCons HBranch HMonoShift PM). }
  destruct (source_full_oc_witness_upper M eb ec en phi' oc' matrix' leastbody profile'
    (succM M count) (succM M s) (succM M x) (succM M u) input' upper'
    HB' HO' HM' HSwap HP' HI' HU' PP' PI' PW PU')
    as (member&subset&HMember&HSubset&PMember&PSubset&POrdZero&PPhi).
  destruct (source_role_reopening_total M (code_numeral M 1) (zeroM M)) as (ib&ic&HIdentity).
  pose proof (source_role_instance_identity M phi' ib ic (succM M (succM M (succM M count)))
    HB' HIdentity) as HSelf.
  pose proof (source_full_oc_monotonicity_use M eb ec en phi' mono'
    (succM M (succM M (succM M count))) (succM M u) (zeroM M) (code_numeral M 1)
    ib ic tb tc phi' result' (source_ordinal_predicate_code M) ordU' subset
    HB' HMono HIdentity HSelf HRole' HResult'
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M)) HOrd' HSubset
    PM' POrdZero POrd' PSubset PPhi) as PResult'.
  set (outbound:=succM M (addM M (succM M (succM M count)) u)).
  assert (HResultBound:source_bounded M result outbound).
  { apply (source_role_instance_bounded M phi (zeroM M) u sb sc result
      (succM M (succM M count)) outbound HB HRole HResult).
    - unfold outbound. apply coding_lt_succ_cases. left. apply coding_le_add.
    - unfold outbound. apply coding_zero_lt_succ.
    - unfold outbound. rewrite Arithmetic.add_comm. apply coding_le_add. }
  apply (full_source_ExE M b c n leastbody least result result' cb cc eb ec en).
  - exists (addM M outbound bound). split.
    + exact (source_bounded_monotone M result outbound (addM M outbound bound)
        HResultBound (coding_le_add M outbound bound)).
    + apply (context_bounded_monotone M b c n bound (addM M outbound bound) HCtx).
      rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact PLeast.
  - exact PResult'.
  - exact HEx.
  - exact HCtxShift.
  - exact HCons.
  - exact HResultShift.
Qed.

Print Assumptions source_full_oc_least_range_elimination.
