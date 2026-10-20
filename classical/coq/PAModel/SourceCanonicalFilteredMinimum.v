(** The actual filtered-set minimum deduction with all its constructor
    witnesses generated internally. Only ordinary source proof premises
    remain: a literal membership profile, Ord(A), the fixed Ord-element
    law, and the literal Foundation minimum. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundMonotone
  SchemaConstructorBounds NumericalContexts NumericalInstantiation SourceQuantifierRules
  NumericalSourceFull SourcePropositionalTemplates SourcePropositionalRebase
  SourceFilteredMinimumPrograms SourceFilteredOrdinalProperties SourceOrdinalFilteredMinimum
  SourceOrdinalPredicate SourceLeastOrdinalGoal SourceLeastOrdinalShift
  SourceOrdinalMemberShell SourceFilteredProfileShift SourceFiniteParameters
  SourceLeastOrdinalFixed SourceQfFunctionality SourceFiniteCutoffShift
  SourceWFSeparationConstructor SourceSeparationSubset.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition canonical_filter_environment {A} (phi s a:A) i :=
  match i with 0=>phi | 1=>s | _=>a end.
Definition canonical_filter_member (i:nat) :=
  E_sf SFMember (CEconst 0) (CEadd (CEvar i) (CEconst 1)).
Definition canonical_filter_point := E_sf_iff (canonical_filter_member 1)
  (E_sf SFAnd (canonical_filter_member 2) (CEvar 0)).
Definition canonical_filter_profile := E_sf_all canonical_filter_point.
Definition canonical_raw_minimum := E_sf_ex (E_sf SFAnd (canonical_filter_member 0)
  (E_sf_all (E_sf SFImpl (E_sf_mem 0 1)
    (E_sf SFImpl
      (E_sf SFMember (CEconst 0) (CEadd (CEadd (CEvar 0) (CEconst 1)) (CEconst 1)))
      (CEconst 0))))).

Lemma canonical_filter_member_graph M env i name member :env i=name ->
  (code_relation M env (canonical_filter_member i) member <->
   sf_relation M SFMember (zeroM M) (succM M name) member).
Proof.
  intro E. apply (schema_expression_graph M env SFMember (CEconst 0)
    (CEadd (CEvar i) (CEconst 1)) (zeroM M) (succM M name) member eq_refl).
  apply source_code_successor_graph. change (name=env i). now symmetry.
Qed.

Lemma canonical_filter_profile_split M phi s a allprofile :
  code_relation M (canonical_filter_environment phi s a) canonical_filter_profile allprofile ->
  exists point smem amem,
    sf_relation M SFAll point (zeroM M) allprofile /\
    sf_relation M SFMember (zeroM M) (succM M s) smem /\
    sf_relation M SFMember (zeroM M) (succM M a) amem /\
    code_relation M (schema_env3 smem amem phi)
      (source_prop_expression filtered_minimum_profile) point.
Proof.
  intro H. destruct (schema_expression_quantifier_split M _ SFAll _ allprofile H)
    as (point&HP&HA).
  destruct (code_relation_total M (canonical_filter_member 1)
    (canonical_filter_environment phi s a)) as (smem&HS).
  destruct (code_relation_total M (canonical_filter_member 2)
    (canonical_filter_environment phi s a)) as (amem&HAM).
  exists point,smem,amem. split;[exact HA|]. split.
  - exact (proj1 (canonical_filter_member_graph M _ 1 s smem eq_refl) HS).
  - split.
    + exact (proj1 (canonical_filter_member_graph M _ 2 a amem eq_refl) HAM).
    + assert (HG:forall index,code_relation M (canonical_filter_environment phi s a)
        (match index with 0=>canonical_filter_member 1|1=>canonical_filter_member 2|_=>CEvar 0 end)
        (schema_env3 smem amem phi index)).
      { intros [|[|index]];cbn [schema_env3];try assumption;reflexivity. }
      exact (proj1 (source_prop_expression_with_graph M
        (canonical_filter_environment phi s a)
        (fun index=>match index with 0=>canonical_filter_member 1
          |1=>canonical_filter_member 2|_=>CEvar 0 end)
        (schema_env3 smem amem phi) filtered_minimum_profile HG point) HP).
Qed.

Lemma canonical_raw_minimum_split M s rawex :
  code_relation M (fun _=>s) canonical_raw_minimum rawex ->
  exists rawbody member allexclusion exclusion member01 memberS neg,
    sf_relation M SFEx rawbody (zeroM M) rawex /\
    sf_relation M SFAnd member allexclusion rawbody /\
    sf_relation M SFMember (zeroM M) (succM M s) member /\
    sf_relation M SFAll exclusion (zeroM M) allexclusion /\
    sf_relation M SFImpl member01 neg exclusion /\
    sf_relation M SFMember (zeroM M) (code_numeral M 1) member01 /\
    sf_relation M SFImpl memberS (zeroM M) neg /\
    sf_relation M SFMember (zeroM M) (succM M (succM M s)) memberS.
Proof.
  intro HG. unfold canonical_raw_minimum in HG.
  destruct (schema_expression_quantifier_split M _ SFEx _ rawex HG) as (rawbody&HB&HEx).
  destruct (schema_expression_split M _ SFAnd _ _ rawbody HB) as (member&allexclusion&HM&HA&HAnd).
  destruct (schema_expression_quantifier_split M _ SFAll _ allexclusion HA) as (exclusion&HE&HAll).
  destruct (schema_expression_split M _ SFImpl _ _ exclusion HE) as (member01&neg&H01&HN&HImp).
  destruct (schema_expression_split M _ SFImpl _ _ neg HN) as (memberS&z&HS&HZ&HNeg).
  change (z=zeroM M) in HZ. subst z.
  assert (HMember:sf_relation M SFMember (zeroM M) (succM M s) member).
  { exact (proj1 (canonical_filter_member_graph M (fun _=>s) 0 s member eq_refl) HM). }
  assert (HMem01:sf_relation M SFMember (zeroM M) (code_numeral M 1) member01).
  { exact (proj1 (schema_expression_graph M (fun _=>s) SFMember (CEconst 0) (CEconst 1)
      (zeroM M) (code_numeral M 1) member01 eq_refl eq_refl) H01). }
  assert (HMemS:sf_relation M SFMember (zeroM M) (succM M (succM M s)) memberS).
  { exact (proj1 (schema_expression_graph M (fun _=>s) SFMember (CEconst 0)
      (CEadd (CEadd (CEvar 0) (CEconst 1)) (CEconst 1))
      (zeroM M) (succM M (succM M s)) memberS eq_refl
      (source_code_successor_graph M (fun _=>s) _ (succM M s)
        (source_code_successor_graph M (fun _=>s) (CEvar 0) s eq_refl))) HS). }
  exists rawbody,member,allexclusion,exclusion,member01,memberS,neg. repeat split;assumption.
Qed.

Theorem source_full_canonical_filtered_minimum M b c n k s a phi ordinal law allprofile rawex target :
  context_bounded M b c n k ->coding_lt M s k ->coding_lt M a k ->
  source_bounded M phi (succM M k) ->
  numerical_instantiation M (source_ordinal_predicate_code M) a ordinal ->
  code_relation M (fun _=>a) (least_fixed_parameter_expression LeastOrdinalMember) law ->
  code_relation M (canonical_filter_environment phi s a) canonical_filter_profile allprofile ->
  code_relation M (fun _=>s) canonical_raw_minimum rawex ->
  source_least_ordinal_graph M phi target ->
  source_full_prv M b c n allprofile ->source_full_prv M b c n ordinal ->
  source_full_prv M b c n law ->source_full_prv M b c n rawex ->
  source_full_prv M b c n target.
Proof.
  intros HC HS HA HB HOrdinal HLaw HProfile HRaw HGoal PP PO PL PR.
  destruct HGoal as (inserted&HInserted&HGoal).
  destruct (source_least_ordinal_expression_split M phi inserted target HGoal)
    as (targetbody&tagged&allconclusion&conclusion&negphi&member01
      &HTargetEx&HTarget&HTagged&HAllConclusion&HConclusion&HMem01&HNegPhi).
  destruct (source_ordinal_member_shell M (fun _=>a) law HLaw)
    as (ordA&allproperties&properties&amem&pair&allinclusion&inclusion&mem01&gmemA
      &HOrdA&HLawGraph&HAllProperties&HAmem&HProperties&HPropertiesPair&HAllInclusion
      &HMem01'&HGmemA&HInclusion).
  pose proof (numerical_instantiation_functional M _ a ordA ordinal HOrdA HOrdinal) as EO.
  subst ordA.
  pose proof (sf_relation_functional M SFMember _ _ mem01 member01 HMem01' HMem01) as EM.
  subst mem01.
  destruct (canonical_filter_profile_split M phi s a allprofile HProfile)
    as (point&smem&amem'&HAllProfile&HSmem&HAmem'&HPoint).
  pose proof (sf_relation_functional M SFMember _ _ amem' amem HAmem' HAmem) as EA.
  subst amem'.
  destruct (canonical_raw_minimum_split M s rawex HRaw)
    as (rawbody&smem'&allexclusion&exclusion&mem01'&gmemS&negS
      &HRawEx&HRawBody&HSmem'&HAllExclusion&HExclusion&HMem01''&HNegS&HGmemS).
  pose proof (sf_relation_functional M SFMember _ _ smem' smem HSmem' HSmem) as ES.
  subst smem'.
  pose proof (sf_relation_functional M SFMember _ _ mem01' member01 HMem01'' HMem01) as EM.
  subst mem01'.
  destruct (sf_relation_total M SFMember (zeroM M) (succM M (succM M a))) as (gmemA'&HGmemA').
  pose proof (sf_relation_functional M SFMember _ _ gmemA' gmemA HGmemA' HGmemA) as EGA.
  subst gmemA'.
  set (rho:=fun index=>match index with 0=>gmemS|1=>gmemA|2=>inserted|_=>member01 end).
  set (rhom:=fun index=>match index with 0=>smem|1=>amem|2=>phi
    |3=>source_ordinal_predicate_code M|_=>allinclusion end).
  destruct (code_relation_total M (source_prop_expression filtered_minimum_profile) rho)
    as (profile&HShiftedPoint).
  destruct (sf_relation_total M SFAll profile (zeroM M)) as (shiftedprofile&HShiftedAll).
  destruct (sf_relation_total M SFImpl smem allinclusion) as (subsetimp&HSubsetImp).
  destruct (sf_relation_total M SFAll subsetimp (zeroM M)) as (subsetall&HSubsetAll).
  destruct (sf_relation_total M SFImpl smem (source_ordinal_predicate_code M)) as (decorationimp&HDecImp).
  destruct (sf_relation_total M SFAll decorationimp (zeroM M)) as (decorationall&HDecAll).
  assert (HShiftedPoint':code_relation M (schema_env3 gmemS gmemA inserted)
    (source_prop_expression separation_point_template) profile).
  { exact HShiftedPoint. }
  assert (HPoint':code_relation M (schema_env3 smem amem phi)
    (source_prop_expression separation_point_template) point) by exact HPoint.
  pose proof (source_filtered_profile_shift M s a phi inserted smem amem point allprofile
    gmemS gmemA profile shiftedprofile HInserted HSmem HAmem HPoint' HAllProfile
    HGmemS HGmemA HShiftedPoint' HShiftedAll) as HShift.
  assert (HIncl:code_relation M rho (source_prop_expression filtered_minimum_inclusion) inclusion).
  { exact (source_prop_template_join M rho SFImpl (SPTSlot 3) (SPTSlot 1)
      member01 gmemA inclusion eq_refl eq_refl HInclusion). }
  assert (HExc:code_relation M rho (source_prop_expression filtered_minimum_exclusion) exclusion).
  { refine (source_prop_template_join M rho SFImpl (SPTSlot 3) (SPTImpl (SPTSlot 0) SPTFalse)
      member01 negS exclusion eq_refl _ HExclusion).
    exact (source_prop_template_join M rho SFImpl (SPTSlot 0) SPTFalse gmemS (zeroM M) negS
      eq_refl eq_refl HNegS). }
  assert (HConc:code_relation M rho (source_prop_expression filtered_predicate_exclusion) conclusion).
  { refine (source_prop_template_join M rho SFImpl (SPTSlot 3) (SPTImpl (SPTSlot 2) SPTFalse)
      member01 negphi conclusion eq_refl _ HConclusion).
    exact (source_prop_template_join M rho SFImpl (SPTSlot 2) SPTFalse inserted (zeroM M) negphi
      eq_refl eq_refl HNegPhi). }
  assert (HProps:code_relation M rhom (source_prop_expression filtered_member_properties) properties).
  { refine (source_prop_template_join M rhom SFImpl (SPTSlot 1) (SPTAnd (SPTSlot 3) (SPTSlot 4))
      amem pair properties eq_refl _ HProperties).
    exact (source_prop_template_join M rhom SFAnd (SPTSlot 3) (SPTSlot 4)
      (source_ordinal_predicate_code M) allinclusion pair eq_refl eq_refl HPropertiesPair). }
  assert (HMember01Bound:source_bounded M member01 (succM M (succM M k))).
  { apply (proj2 (source_bounded_accept_atom M SFMember _ _ member01 _ (or_introl eq_refl) HMem01)).
    split;[apply coding_zero_lt_succ|].
    exact (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M k)) (coding_zero_lt_succ M k)). }
  assert (HGAS:source_bounded M gmemA (succM M (succM M k))).
  { apply (proj2 (source_bounded_accept_atom M SFMember _ _ gmemA _ (or_introl eq_refl) HGmemA)).
    split;[apply coding_zero_lt_succ|]. repeat apply (proj2 (coding_lt_succ_cancel M _ _)). exact HA. }
  assert (HGSS:source_bounded M gmemS (succM M (succM M k))).
  { apply (proj2 (source_bounded_accept_atom M SFMember _ _ gmemS _ (or_introl eq_refl) HGmemS)).
    split;[apply coding_zero_lt_succ|]. repeat apply (proj2 (coding_lt_succ_cancel M _ _)). exact HS. }
  assert (HIncludedBound:source_bounded M allinclusion (succM M k)).
  { apply (proj2 (source_bounded_accept_unary M SFAll inclusion allinclusion _
      (or_introl eq_refl) HAllInclusion)).
    apply (proj2 (source_bounded_accept_binary M SFImpl member01 gmemA inclusion _
      (or_intror (or_intror eq_refl)) HInclusion)). auto. }
  assert (HOrdBound:source_bounded M (source_ordinal_predicate_code M) (succM M k)).
  { exact (source_bounded_monotone M _ (code_numeral M 1) (succM M k)
      (source_ordinal_predicate_bounded M)
      (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M k)) (coding_zero_lt_succ M k))). }
  assert (HRho:forall index,source_bounded M (rho index) (succM M (succM M k))).
  { intros [|[|[|index]]];cbn [rho];try assumption.
    exact (source_cutoff_shift_bounded M 1 phi inserted k HB HInserted). }
  assert (HRhom:forall index,source_bounded M (rhom index) (succM M k)).
  { intros [|[|[|[|index]]]];cbn [rhom];try assumption.
    - apply (proj2 (source_bounded_accept_atom M SFMember _ _ smem _ (or_introl eq_refl) HSmem)).
      split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M s k) HS)].
    - apply (proj2 (source_bounded_accept_atom M SFMember _ _ amem _ (or_introl eq_refl) HAmem)).
      split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M a k) HA)]. }
  exact (source_full_ordinal_filtered_minimum M rho rhom k b c n
    profile allprofile shiftedprofile point inclusion allinclusion subsetimp subsetall
    exclusion allexclusion rawbody rawex conclusion allconclusion
    (source_ordinal_predicate_code M) decorationimp decorationall tagged targetbody target
    ordinal properties allproperties law HC HRho HRhom HShiftedPoint HShiftedAll HShift
    HAllProfile HPoint HIncl HAllInclusion HSubsetImp HSubsetAll HExc HAllExclusion
    HRawBody HRawEx HConc HAllConclusion HOrdBound HDecImp HDecAll HTagged HTarget HTargetEx
    eq_refl eq_refl HProps HAllProperties HLawGraph PP PO PL PR).
Qed.

Print Assumptions canonical_filter_member_graph.
Print Assumptions canonical_filter_profile_split.
Print Assumptions canonical_raw_minimum_split.
Print Assumptions source_full_canonical_filtered_minimum.
