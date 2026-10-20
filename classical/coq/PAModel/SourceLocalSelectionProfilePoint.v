(** Actual selected-set profile for an arbitrary represented source matrix.
    Both Op5 and SC correctness are derived from genuine source proofs in
    the included finite ZFR context; no profile/correctness premise remains. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityBounds SourceDefinabilityStep NumericalEnvironments NumericalSubstitution
 NumericalSourceFull SourceRoleReopening SourceRepresentationRecipe SourceEnvInClosureConstructor
 SourceDnEliminationInvariant SourceSetRelativization SourceIffGraphs NumericalContexts SourceNamedVacuity
 SourceSelectionSCBinder SourceLocalDefinabilityContext SourceSelectionRepresentationGuard
 SourceSelectionOperationGraph SourceLocalSelectionOperationUse SourceSelectionProfileLogic
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceBooleanIffPrograms.
Unset Implicit Arguments.
Definition local_selection_profile_values M inSelected inCarrier selection matrix i:=match i with
 |0=>inSelected|1=>inCarrier|2=>selection|3=>matrix|_=>zeroM M end.
Theorem source_full_local_selection_profile_point M count phi rep d X rb rc assignedRep pb pc value vb vc
 environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
 fb fc fn gb gc gn k sc final guard selected operation inSelected rawPair rawProfile newPair profile:
 source_bounded M phi(succM M count) ->source_representation_recipe M(succM M count)phi rep ->
 source_role_reopening M X d rb rc ->
 numerical_substitution M rep rb rc(code_numeral M 2)(code_numeral M 2)assignedRep ->
 source_envf M count environment ->source_envf M(succM M count)next ->source_def_step M true environment next ->
 environment_cons M pb pc count value vb vc(succM M count) ->
 environment_cons M pb pc count old ob oc(succM M count) ->
 environment_cons M vb vc(succM M count)new nb nc(succM M(succM M count)) ->
 numerical_substitution M environment ob oc(succM M count)(zeroM M)previous ->
 numerical_substitution M next nb nc(succM M(succM M count))(zeroM M)target ->
 code_relation M(EIC_ext_roles old new value)EIC_ext_expression extension ->
 old<>new ->value<>old ->(forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old) ->
 numerical_substitution M phi vb vc(succM M count)(zeroM M)assignedPhi ->
 source_set_relativization M X assignedPhi relative ->source_bounded M relative k ->
 sf_relation M SFMember value X memberValue ->sf_relation M SFMember new d memberResult ->
 source_iff_graph M memberResult relative result ->
 source_full_prv M gb gc gn assignedRep ->source_dn_parameter_proofs M count pb pc X gb gc gn ->
 source_full_prv M gb gc gn previous ->
 source_named_context_vacuous M gb gc gn new ->context_bounded M gb gc gn k ->
 source_bounded M extension k ->source_bounded M memberResult k ->source_bounded M memberValue k ->
 source_named_vacuous M new relative ->
 new<>value ->new<>X ->new<>d ->
 code_relation M(local_SC_names d old value)source_local_SC_expression sc ->
 source_iff_graph M sc relative final ->source_local_fixed_context M fb fc fn ->
 context_included M fb fc fn gb gc gn ->sf_relation M SFImpl memberValue final guard ->
 code_relation M(local_operation5_names d old X selected)source_local_operation5_expression operation ->
 sf_relation M SFMember value selected inSelected ->source_bounded M inSelected k ->source_bounded M sc k ->
 sf_relation M SFAnd memberValue sc rawPair ->source_iff_graph M inSelected rawPair rawProfile ->
 sf_relation M SFAnd memberValue relative newPair ->source_iff_graph M inSelected newPair profile ->
 source_full_prv M gb gc gn operation ->source_full_prv M gb gc gn profile.
Proof.
 intros BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt HOldNew HValueOld HFresh
  HAssigned HRelative BRelative HMemberValue HMemberResult HResult PRep HMembers POld
  VCtx BC BE BM BV VT HNewValue HNewX HNewD HSC HFinal HFixed HIncluded HGuard
  HOp HInSelected BInSelected BSC HRawPair HRawProfile HNewPair HProfile POp.
 pose proof(source_full_selection_representation_guard M count phi rep d X rb rc assignedRep pb pc value vb vc
  environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
  fb fc fn gb gc gn k sc final guard BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt
  HOldNew HValueOld HFresh HAssigned HRelative BRelative HMemberValue HMemberResult HResult
  PRep HMembers POld VCtx BC BE BM BV VT HNewValue HNewX HNewD HSC HFinal HFixed HIncluded HGuard)as PGuard.
 pose proof(source_full_local_selection_operation M fb fc fn gb gc gn d old X selected value operation inSelected memberValue
  sc rawPair rawProfile k HFixed HIncluded BC HOp HInSelected HMemberValue HSC HRawPair HRawProfile POp)as PRaw.
 set(values:=local_selection_profile_values M inSelected memberValue sc relative).
 assert(BValues:forall i,source_bounded M(values i)k).
 { intros[|[|[|[|i]]]];cbn[values local_selection_profile_values];try assumption;apply source_bounded_accept_falsity. }
 assert(GPair:code_relation M values(source_prop_expression(SPTAnd(SPTSlot 1)(SPTSlot 2)))rawPair).
 { exact(source_prop_template_join M values SFAnd(SPTSlot 1)(SPTSlot 2)memberValue sc rawPair eq_refl eq_refl HRawPair). }
 assert(GNewPair:code_relation M values(source_prop_expression(SPTAnd(SPTSlot 1)(SPTSlot 3)))newPair).
 { exact(source_prop_template_join M values SFAnd(SPTSlot 1)(SPTSlot 3)memberValue relative newPair eq_refl eq_refl HNewPair). }
 assert(GRaw:code_relation M values(source_prop_expression selection_profile_raw)rawProfile).
 { exact(source_tv_iff_template_graph M values(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 2))inSelected rawPair rawProfile
    eq_refl GPair HRawProfile). }
 assert(GGuard:code_relation M values(source_prop_expression selection_profile_guard)guard).
 { apply(source_prop_template_join M values SFImpl(SPTSlot 1)(SPTIff(SPTSlot 2)(SPTSlot 3))memberValue final guard eq_refl);[|exact HGuard].
   exact(source_tv_iff_template_graph M values(SPTSlot 2)(SPTSlot 3)sc relative final eq_refl eq_refl HFinal). }
 assert(GProfile:code_relation M values(source_prop_expression selection_profile_result)profile).
 { exact(source_tv_iff_template_graph M values(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTSlot 3))inSelected newPair profile
    eq_refl GNewPair HProfile). }
 exact(source_full_selection_profile_logic M gb gc gn values rawProfile guard profile k BValues BC GRaw GGuard GProfile PRaw PGuard).
Qed.
Print Assumptions source_full_local_selection_profile_point.
