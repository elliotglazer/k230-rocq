(** The actual local definability point used by the Op5 selection.
    An Ext0 witness of the old assigned environment satisfies the new
    EnvF constructor, so representation gives its membership iff matrix.
    No correctness theorem is an additional premise. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityBounds SourceDefinabilityStep NumericalEnvironments NumericalSubstitution
 NumericalSourceFull SourceRoleReopening SourceRepresentationRecipe SourceRepresentationQuery
 SourceEnvAssignmentProof SourceEnvInClosureConstructor SourceDnEliminationInvariant
 SourceSetRelativization SourceIffGraphs.
Unset Implicit Arguments.
Theorem source_full_selection_representation_point M count phi rep d X rb rc assignedRep pb pc value vb vc
 environment next old ob oc previous new nb nc target extension memberValue memberResult relative assignedPhi result
 gb gc gn k:
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
 source_full_prv M gb gc gn extension ->source_full_prv M gb gc gn result.
Proof.
 intros BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt HOldNew HValueOld HFresh
  HAssigned HRelative BRelative HMemberValue HMemberResult HResult PRep HMembers PValue POld PExt.
 pose proof(source_full_env_assignment_extension M count environment next pb pc value vb vc
  old ob oc previous new nb nc target extension gb gc gn HE HStep HV HO HN HP HT HExt HOldNew HValueOld
  HFresh POld PExt)as PTarget.
 exact(source_full_representation_query M(succM M count)phi rep d X rb rc assignedRep vb vc next new nb nc
  target assignedPhi relative memberResult result gb gc gn k BF HRep HOpen HAssignedRep HNext HN HT
  HAssigned HRelative BRelative HMemberResult HResult PRep
  (source_dn_parameter_proofs_cons M count pb pc value vb vc X gb gc gn memberValue HV HMemberValue PValue HMembers)
  PTarget).
Qed.
Print Assumptions source_full_selection_representation_point.
