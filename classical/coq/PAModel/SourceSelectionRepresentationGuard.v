(** Discharge the tested-value carrier premise from actual SC correctness.
    Only the genuine guarded SC iff remains, with no source proof family. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityBounds SourceDefinabilityStep NumericalEnvironments NumericalSubstitution
 NumericalSourceFull SourceRoleReopening SourceRepresentationRecipe SourceEnvInClosureConstructor
 SourceDnEliminationInvariant SourceSetRelativization SourceIffGraphs NumericalContexts SourceNamedVacuity
 SourceSelectionSCBinder SourceSelectionRepresentationSCFixed SourceLocalDefinabilityContext
 SourceContextProofHelpers SourceNamedElimination SourceFiniteFamilyBounds SourceUpperProofHelpers.
Unset Implicit Arguments.
Theorem source_full_selection_representation_guard M count phi rep d X rb rc assignedRep pb pc value vb vc
 environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
 fb fc fn gb gc gn k sc final guard:
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
 source_full_prv M gb gc gn guard.
Proof.
 intros BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt HOldNew HValueOld HFresh
  HAssigned HRelative BRelative HMemberValue HMemberResult HResult PRep HMembers POld
  VCtx BC BE BM BV VT HNewValue HNewX HNewD HSC HFinal HFixed HIncluded HGuard.
 destruct(environment_cons_total M gb gc gn memberValue)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M gb gc gn memberValue ub uc un k HCons)(conj BV BC))as BU.
 pose proof(source_full_cons_head M gb gc gn memberValue ub uc un k HCons BV BU)as PValue.
 pose proof(source_full_cons_weaken M gb gc gn memberValue ub uc un k assignedRep HCons BU PRep)as PRep'.
 pose proof(source_full_cons_weaken M gb gc gn memberValue ub uc un k previous HCons BU POld)as POld'.
 assert(HMembers':source_dn_parameter_proofs M count pb pc X ub uc un).
 { intros i v member HI HValue HMember.
   exact(source_full_cons_weaken M gb gc gn memberValue ub uc un k member HCons BU
    (HMembers i v member HI HValue HMember)). }
 assert(VMember:source_named_vacuous M new memberValue).
 { exact(source_named_member_vacuous M value X memberValue new
   (fun E=>HNewValue(eq_sym E))(fun E=>HNewX(eq_sym E))HMemberValue). }
 pose proof(source_named_context_vacuous_cons M gb gc gn memberValue ub uc un new HCons VCtx VMember)as VU.
 assert(HIncluded':context_included M fb fc fn ub uc un).
 { intros f HF. apply(proj2(context_member_cons M gb gc gn memberValue ub uc un f HCons)).
   right. exact(HIncluded f HF). }
 pose proof(source_full_selection_representation_SC_fixed M count phi rep d X rb rc assignedRep pb pc value vb vc
  environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
  fb fc fn ub uc un k sc final BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt
  HOldNew HValueOld HFresh HAssigned HRelative BRelative HMemberValue HMemberResult HResult
  PRep' HMembers' PValue POld' VU BU BE BM VT HNewValue HNewD HSC HFinal HFixed HIncluded')as PFinal.
 exact(source_full_implication_intro M gb gc gn memberValue final guard ub uc un HCons HGuard PFinal).
Qed.
Print Assumptions source_full_selection_representation_guard.
