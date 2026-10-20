(** Retain an additional unary property, for example Ord(m), when transferring an actual Foundation minimum of a filtered set to an
    existential minimum of its defining predicate. The subset premise is
    the ordinary formula forall m (m in S -> m subset A), not a proof
    transformer. All graphs refer to actual source syntax. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalInstantiation SourceQuantifierRules SourceSequents
  SourceProofRenaming SourceProofWeakening NumericalSourceFull
  SourcePropositionalTemplates SourceUniversalPropositional SourceExistentialMap
  SourceFilteredMinimumPrograms SourceFilteredMinimum.
Unset Implicit Arguments.

Theorem source_full_decorated_filtered_minimum_exists M rho rhom k b c n
    profile allprofile shiftedprofile point
    inclusion allinclusion subsetimp subsetall
    exclusion allexclusion rawbody rawex
    conclusion allconclusion decoration decorationimp decorationall tagged targetbody targetex :
  context_bounded M b c n k ->
  (forall i,source_bounded M (rho i) (succM M (succM M k))) ->
  (forall i,source_bounded M (rhom i) (succM M k)) ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) profile ->
  sf_relation M SFAll profile (zeroM M) shiftedprofile ->
  source_formula_shift M allprofile shiftedprofile ->
  numerical_instantiation M profile (zeroM M) point ->
  code_relation M rhom (source_prop_expression filtered_minimum_profile) point ->
  code_relation M rho (source_prop_expression filtered_minimum_inclusion) inclusion ->
  sf_relation M SFAll inclusion (zeroM M) allinclusion ->
  sf_relation M SFImpl (rhom 0) allinclusion subsetimp ->
  sf_relation M SFAll subsetimp (zeroM M) subsetall ->
  code_relation M rho (source_prop_expression filtered_minimum_exclusion) exclusion ->
  sf_relation M SFAll exclusion (zeroM M) allexclusion ->
  sf_relation M SFAnd (rhom 0) allexclusion rawbody ->
  sf_relation M SFEx rawbody (zeroM M) rawex ->
  code_relation M rho (source_prop_expression filtered_predicate_exclusion) conclusion ->
  sf_relation M SFAll conclusion (zeroM M) allconclusion ->
  source_bounded M decoration (succM M k) ->
  sf_relation M SFImpl (rhom 0) decoration decorationimp ->
  sf_relation M SFAll decorationimp (zeroM M) decorationall ->
  sf_relation M SFAnd decoration (rhom 2) tagged ->
  sf_relation M SFAnd tagged allconclusion targetbody ->
  sf_relation M SFEx targetbody (zeroM M) targetex ->
  source_full_prv M b c n allprofile -> source_full_prv M b c n subsetall ->
  source_full_prv M b c n rawex -> source_full_prv M b c n decorationall ->
  source_full_prv M b c n targetex.
Proof.
  intros HC HB HBM HP HAP HSP HInst HPoint HI HAI HSub HSubAll
    HE HAE HRaw HRawEx HD HAD HDec HDecImp HDecAll HTagged HTarget HTargetEx PP PSub PRaw PDecAll.
  pose proof (source_prop_template_bound M rho filtered_minimum_exclusion
    (succM M (succM M k)) HB exclusion HE) as HEB.
  pose proof (proj2 (source_bounded_accept_unary M SFAll exclusion allexclusion
    (succM M k) (or_introl eq_refl) HAE) HEB) as HAEB.
  assert (HRawBound:source_bounded M rawbody (succM M k)).
  { apply (proj2 (source_bounded_accept_binary M SFAnd (rhom 0) allexclusion rawbody
      (succM M k) (or_introl eq_refl) HRaw)). split;[exact (HBM 0)|exact HAEB]. }
  pose proof (source_prop_template_bound M rho filtered_predicate_exclusion
    (succM M (succM M k)) HB conclusion HD) as HDB.
  pose proof (proj2 (source_bounded_accept_unary M SFAll conclusion allconclusion
    (succM M k) (or_introl eq_refl) HAD) HDB) as HADB.
  assert (HTaggedBound:source_bounded M tagged (succM M k)).
  { apply (proj2 (source_bounded_accept_binary M SFAnd decoration (rhom 2) tagged
      (succM M k) (or_introl eq_refl) HTagged)). split;[exact HDec|exact (HBM 2)]. }
  assert (HTargetBound:source_bounded M targetbody (succM M k)).
  { apply (proj2 (source_bounded_accept_binary M SFAnd tagged allconclusion targetbody
      (succM M k) (or_introl eq_refl) HTarget)). split;[exact HTaggedBound|exact HADB]. }
  assert (HTargetWF:source_sequent_wf M b c n targetex).
  { exists k. split;[|exact HC].
    exact (proj2 (source_bounded_accept_unary M SFEx targetbody targetex k
      (or_intror eq_refl) HTargetEx) HTargetBound). }
  destruct (context_shift_total M b c n) as (sb&sc&HShift).
  destruct (environment_cons_total M sb sc n rawbody) as (ub&uc&un&HCons).
  destruct (numerical_renaming_total M targetex (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [shiftedtarget HShiftTarget].
  assert (HSBC:context_bounded M sb sc n (succM M k))
    by (exact (context_shift_preserves_bound M b c n sb sc k HShift HC)).
  assert (HUBC:context_bounded M ub uc un (succM M k)).
  { apply (proj2 (context_bounded_cons M sb sc n rawbody ub uc un (succM M k) HCons)). auto. }
  assert (Weak:forall f,source_full_prv M sb sc n f ->source_full_prv M ub uc un f).
  { intros f PF. apply (source_full_prv_weaken_bounded M sb sc n ub uc un f (succM M k) PF).
    - intros q HQ. apply (proj2 (context_member_cons M sb sc n rawbody ub uc un q HCons)). now right.
    - exact HUBC. }
  assert (PRawBody:source_full_prv M ub uc un rawbody).
  { apply full_source_Ctx;[exists (succM M k);auto|].
    apply (proj2 (context_member_cons M sb sc n rawbody ub uc un rawbody HCons)). now left. }
  assert (PIn:source_full_prv M ub uc un (rhom 0)).
  { apply (full_source_CE1 M ub uc un (rhom 0) allexclusion rawbody).
    - exists (succM M k). split;[exact (HBM 0)|exact HUBC].
    - exact PRawBody.
    - exact HRaw. }
  assert (PExcluded:source_full_prv M ub uc un allexclusion).
  { apply (full_source_CE2 M ub uc un (rhom 0) allexclusion rawbody).
    - exists (succM M k). auto.
    - exact PRawBody.
    - exact HRaw. }
  assert (PProfile:source_full_prv M ub uc un shiftedprofile).
  { apply Weak. exact (source_full_prv_renaming M b c n allprofile
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M))
      sb sc shiftedprofile PP HShift HSP). }
  assert (PSubsetImp:source_full_prv M ub uc un subsetimp).
  { apply Weak. exact (source_full_all_shift M b c n subsetimp subsetall sb sc
      HSubAll PSub HShift). }
  assert (PSubset:source_full_prv M ub uc un allinclusion).
  { apply (full_source_IE M ub uc un (rhom 0) allinclusion subsetimp).
    - exists (succM M k). split;[|exact HUBC].
      apply (proj2 (source_bounded_accept_unary M SFAll inclusion allinclusion
        (succM M k) (or_introl eq_refl) HAI)).
      exact (source_prop_template_bound M rho filtered_minimum_inclusion
        (succM M (succM M k)) HB inclusion HI).
    - exact PSubsetImp.
    - exact PIn.
    - exact HSub. }
  pose proof (proj2 (source_full_filtered_member_specialization M rhom (succM M k)
    ub uc un profile shiftedprofile (zeroM M) point
    HBM HUBC HAP HInst HPoint PProfile PIn)) as PPredicate.
  pose proof (source_full_filtered_minimum_exclusion M rho (succM M k) ub uc un
    profile shiftedprofile inclusion allinclusion exclusion allexclusion conclusion allconclusion
    HB HUBC HP HI HE HD HAP HAI HAE HAD PProfile PSubset PExcluded) as PConclusion.
  assert (PDecoration:source_full_prv M ub uc un decoration).
  { apply (full_source_IE M ub uc un (rhom 0) decoration decorationimp).
    - exists (succM M k). auto.
    - apply Weak. exact (source_full_all_shift M b c n decorationimp decorationall sb sc
        HDecAll PDecAll HShift).
    - exact PIn.
    - exact HDecImp. }
  assert (PTagged:source_full_prv M ub uc un tagged).
  { apply (full_source_CI M ub uc un decoration (rhom 2) tagged).
    - exists (succM M k). auto.
    - exact PDecoration.
    - exact PPredicate.
    - exact HTagged. }
  apply (source_full_exists_map M b c n rawbody targetbody rawex targetex
    sb sc ub uc un shiftedtarget HTargetWF HRawEx HTargetEx HShift HCons HShiftTarget PRaw).
  apply (full_source_CI M ub uc un tagged allconclusion targetbody).
  - exists (succM M k). auto.
  - exact PTagged.
  - exact PConclusion.
  - exact HTarget.
Qed.

Print Assumptions source_full_decorated_filtered_minimum_exists.
