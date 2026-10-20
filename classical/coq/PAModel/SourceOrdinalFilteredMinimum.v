(** The ordinal filtered-minimum deduction consumes the actual fixed
    ordinal-element law and Foundation minimum proof. Subset/ordinal branch
    properties and shifted-profile specialization are proved internally. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetCodeDescent SourceBounded NumericalContexts NumericalInstantiation
  SourceInstantiationConstructors SourceQuantifierRules SourceShiftSpecialization
  NumericalSourceFull SourcePropositionalTemplates SourceFilteredMinimumPrograms
  SourceFilteredOrdinalProperties SourceDecoratedFilteredMinimum.
Unset Implicit Arguments.

Theorem source_full_ordinal_filtered_minimum M rho rhom k b c n
    profile allprofile shiftedprofile point
    inclusion allinclusion subsetimp subsetall
    exclusion allexclusion rawbody rawex
    conclusion allconclusion decoration decorationimp decorationall tagged targetbody targetex
    ordinal properties allproperties fixedlaw :
  context_bounded M b c n k ->
  (forall i,source_bounded M (rho i) (succM M (succM M k))) ->
  (forall i,source_bounded M (rhom i) (succM M k)) ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) profile ->
  sf_relation M SFAll profile (zeroM M) shiftedprofile ->
  source_formula_shift M allprofile shiftedprofile ->
  sf_relation M SFAll point (zeroM M) allprofile ->
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
  rhom 3=decoration -> rhom 4=allinclusion ->
  code_relation M rhom (source_prop_expression filtered_member_properties) properties ->
  sf_relation M SFAll properties (zeroM M) allproperties ->
  sf_relation M SFImpl ordinal allproperties fixedlaw ->
  source_full_prv M b c n allprofile -> source_full_prv M b c n ordinal ->
  source_full_prv M b c n fixedlaw -> source_full_prv M b c n rawex ->
  source_full_prv M b c n targetex.
Proof.
  intros HC HB HBM HP HAP HSP HOriginal HPoint HI HAI HSub HSubAll
    HE HAE HRaw HRawEx HD HAD HDec HDecImp HDecAll HTagged HTarget HTargetEx
    EDec EIncl HProperties HAllProperties HLaw PP POrdinal PLaw PRaw.
  assert (PProperties:source_full_prv M b c n allproperties).
  { apply (full_source_IE M b c n ordinal allproperties fixedlaw).
    - exact (source_wf_binary_right M b c n SFImpl ordinal allproperties fixedlaw
        ltac:(unfold sf_binary;auto) HLaw (source_full_prv_wellformed M b c n fixedlaw PLaw)).
    - exact PLaw.
    - exact POrdinal.
    - exact HLaw. }
  assert (HSubCode:code_relation M rhom
    (source_prop_expression (filtered_member_has_property 4)) subsetimp).
  { apply (source_prop_template_join M rhom SFImpl (SPTSlot 0) (SPTSlot 4)
      (rhom 0) allinclusion subsetimp eq_refl (eq_sym EIncl) HSub). }
  assert (HDecCode:code_relation M rhom
    (source_prop_expression (filtered_member_has_property 3)) decorationimp).
  { apply (source_prop_template_join M rhom SFImpl (SPTSlot 0) (SPTSlot 3)
      (rhom 0) decoration decorationimp eq_refl (eq_sym EDec) HDecImp). }
  pose proof (source_full_filtered_member_property M rhom k b c n 4
    point allprofile properties allproperties subsetimp subsetall (or_intror eq_refl)
    HBM HC HPoint HProperties HSubCode HOriginal HAllProperties HSubAll PP PProperties) as PSubset.
  pose proof (source_full_filtered_member_property M rhom k b c n 3
    point allprofile properties allproperties decorationimp decorationall (or_introl eq_refl)
    HBM HC HPoint HProperties HDecCode HOriginal HAllProperties HDecAll PP PProperties) as PDecoration.
  pose proof (source_prop_template_bound M rhom filtered_minimum_profile
    (succM M k) HBM point HPoint) as HPointBound.
  destruct (source_shifted_all_specialization M point allprofile shiftedprofile (succM M k)
    HPointBound HOriginal HSP) as [shiftedbody [HShiftedBody HInstance]].
  pose proof (proj1 (proj2 (sf_relation_injective M SFAll SFAll profile (zeroM M)
    shiftedbody (zeroM M) shiftedprofile HAP HShiftedBody))) as EBody. subst shiftedbody.
  exact (source_full_decorated_filtered_minimum_exists M rho rhom k b c n
    profile allprofile shiftedprofile point inclusion allinclusion subsetimp subsetall
    exclusion allexclusion rawbody rawex conclusion allconclusion
    decoration decorationimp decorationall tagged targetbody targetex
    HC HB HBM HP HAP HSP HInstance HPoint HI HAI HSub HSubAll HE HAE HRaw HRawEx
    HD HAD HDec HDecImp HDecAll HTagged HTarget HTargetEx PP PSubset PRaw PDecoration).
Qed.
Print Assumptions source_full_ordinal_filtered_minimum.

