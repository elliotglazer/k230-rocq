(** Actual SC correctness for a represented source matrix, at an arbitrary
    internal assignment. All universal/witness logic is discharged; Ext0
    existence remains an ordinary, finite source-proof input in this context. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityBounds SourceDefinabilityStep NumericalEnvironments NumericalSubstitution
 NumericalSourceFull SourceRoleReopening SourceRepresentationRecipe SourceEnvInClosureConstructor
 SourceDnEliminationInvariant SourceSetRelativization SourceIffGraphs NumericalContexts SourceNamedVacuity
 SourceNamedQuantifierRules SourceSelectionSCBinder SourceSelectionRepresentationAll SourceNamedSelectionEquivalence.
Unset Implicit Arguments.
Theorem source_full_selection_representation_SC M count phi rep d X rb rc assignedRep pb pc value vb vc
 environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
 gb gc gn k exExtension sc final:
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
 source_full_prv M gb gc gn memberValue ->source_full_prv M gb gc gn previous ->
 source_named_context_vacuous M gb gc gn new ->context_bounded M gb gc gn k ->
 source_bounded M extension k ->source_bounded M memberResult k ->source_named_vacuous M new relative ->
 new<>value ->new<>d ->source_named_quantifier M false new extension exExtension ->
 code_relation M(local_SC_names d old value)source_local_SC_expression sc ->
 source_iff_graph M sc relative final ->source_full_prv M gb gc gn exExtension ->
 source_full_prv M gb gc gn final.
Proof.
 intros BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt HOldNew HValueOld HFresh
  HAssigned HRelative BRelative HMemberValue HMemberResult HResult PRep HMembers PValue POld
  VCtx BC BE BM VT HNewValue HNewD HEx HSC HFinal PEx.
 destruct(sf_relation_total M SFImpl extension result)as(point&HPoint).
 destruct(source_named_quantifier_total M true new point)as(all&HAll).
 pose proof(source_full_selection_representation_all M count phi rep d X rb rc assignedRep pb pc value vb vc
  environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
  gb gc gn k point all k BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt
  HOldNew HValueOld HFresh HAssigned HRelative BRelative HMemberValue HMemberResult HResult
  PRep HMembers PValue POld VCtx BC BE HPoint HAll)as PAll.
 destruct(sf_relation_total M SFAnd memberResult extension)as(pair&HPair).
 assert(HScNamed:source_named_quantifier M false new pair sc).
 { exact(source_local_SC_named_binder M d old value new extension memberResult pair sc
    HNewD(fun E=>HOldNew(eq_sym E))HNewValue HExt HMemberResult HPair HSC). }
 exact(source_full_named_selection_equivalence M gb gc gn new extension memberResult relative result point all
  exExtension pair sc final k BC VCtx BE BM BRelative VT HResult HPoint HAll HEx HPair HScNamed HFinal PAll PEx).
Qed.
Print Assumptions source_full_selection_representation_SC.
