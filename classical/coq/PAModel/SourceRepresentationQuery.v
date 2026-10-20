(** Actual representation correctness at one internally coded assignment.
    Every Dn parameter and the environment quantifier are eliminated in the
    source calculus. Arbitrary matrix syntax and moving-carrier substitution
    are retained literally; there is no quantified correctness premise. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SetFormulaCodes SetSchemaConstructors SourceBounded SourceDefinabilityBounds SourceDefinabilityIteration
 SourceFiniteCutoffShift NumericalEnvironments NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 NumericalInstantiation SubstitutionSource NumericalSourceFull SourceQuantifierRules SourceRoleReopening SourceDn
 SourceDnAssignments SourceDnEliminationInvariant SourceRepresentationRecipe SourceRepresentationAssignment
 SourceRepresentationRelativeShift SourceRepresentationEnvironmentQuery SourceWholeShiftInstantiation
 SourceSetRelativization SourceIffGraphs SourceEnvironmentCarrierClosure SourceInstantiationConstructors SourceDerivedRules.
Unset Implicit Arguments.
Lemma source_instantiation_iff M a b out a' b' out' witness:
 source_iff_graph M a b out ->source_iff_graph M a' b' out' ->
 numerical_instantiation M a witness a' ->numerical_instantiation M b witness b' ->
 numerical_instantiation M out witness out'.
Proof.
 intros HI HO(ib&ic&HH&HA)(jb&jc&HJ&HB). exists ib,ic. split;[exact HH|].
 apply(source_iff_substitution M a b out a' b' out' ib ic(code_numeral M 1)(zeroM M)HI HO HA).
 exact(proj1(numerical_substitution_extensional M b jb jc(code_numeral M 1)ib ic(code_numeral M 1)
  (zeroM M)b'(substitution_singletons_equivalent M jb jc ib ic witness HJ HH))HB).
Qed.
Theorem source_full_representation_query M count phi rep d X rb rc assignedRep pb pc
 environment witness eb ec envAt assignedPhi relative member result gb gc gn k:
 source_bounded M phi count ->source_representation_recipe M count phi rep ->
 source_role_reopening M X d rb rc ->
 numerical_substitution M rep rb rc(code_numeral M 2)(code_numeral M 2)assignedRep ->
 source_envf M count environment ->environment_cons M pb pc count witness eb ec(succM M count) ->
 numerical_substitution M environment eb ec(succM M count)(zeroM M)envAt ->
 numerical_substitution M phi pb pc count(zeroM M)assignedPhi ->
 source_set_relativization M X assignedPhi relative ->source_bounded M relative k ->
 sf_relation M SFMember witness d member ->source_iff_graph M member relative result ->
 source_full_prv M gb gc gn assignedRep ->source_dn_parameter_proofs M count pb pc X gb gc gn ->
 source_full_prv M gb gc gn envAt ->source_full_prv M gb gc gn result.
Proof.
 intros BF(oldEnv&first&shifted&matrix&rawRelative&body&HE&H1&H2&HM&HR&HB&HD)
  HOpen HRep HEnv HCons HAt HAssigned HRelative BRelative HMember HResult PRep HMembers PEnv.
 assert(EE:oldEnv=environment)by(eapply source_def_iteration_functional;eassumption). subst oldEnv.
 destruct(source_dn_assignment_total M count pb pc d X)as(ab&ac&HA).
 destruct(substitution_lift_total M ab ac(succM M(succM M count))(zeroM M))as(lb&lc&ln&HL).
 destruct(numerical_substitution_total M shifted lb lc ln(code_numeral M 1))as(assignedEnv&HAssignedEnv).
 destruct(numerical_renaming_total M relative(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shiftedRelative&HRelativeShift).
 pose proof(source_representation_assigned_relative_shift M count phi matrix rawRelative d X pb pc ab ac lb lc ln
  assignedPhi relative shiftedRelative BF HM HR HA HL HAssigned HRelative HRelativeShift)as HAssignedRelative.
 destruct(code_relation_total M E_assigned_representation_point
  (schema_env3 assignedEnv shiftedRelative(succM M d)))as(point&HPoint).
 pose proof(source_full_representation_assignment M count phi rep d X rb rc assignedRep pb pc ab ac lb lc ln
  environment first shifted matrix rawRelative body assignedEnv shiftedRelative point gb gc gn
  BF HE H1 H2 HM HR HB HD HOpen HRep HA HL HAssignedEnv HAssignedRelative HPoint PRep HMembers)as PPoint.
 pose proof(source_representation_environment_query M count environment first shifted d X pb pc ab ac lb lc ln
  assignedEnv witness eb ec envAt HE H1 H2 HA HL HAssignedEnv HCons HAt)as HEnvQuery.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M d))as(atom&HAtom).
 destruct(source_iff_total M atom shiftedRelative)as(iff&HIff).
 destruct(sf_relation_total M SFImpl assignedEnv iff)as(localbody&HLocal).
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(all&HAll).
 assert(HAllCode:code_relation M(schema_env3 assignedEnv shiftedRelative(succM M d))
   E_assigned_representation_point all).
 { unfold E_assigned_representation_point.
   eapply environment_carrier_code_join;[|reflexivity|exact HAll].
   eapply environment_carrier_code_join;[reflexivity| |exact HLocal].
   destruct(source_iff_parts M atom shiftedRelative iff HIff)as(lr&rl&HLR&HRL&HAnd).
   unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HAnd].
   - eapply environment_carrier_code_join;[|reflexivity|exact HLR].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HAtom].
   - eapply environment_carrier_code_join;[reflexivity| |exact HRL].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HAtom]. }
 assert(EAll:all=point)by(eapply code_relation_functional;eassumption). subst all.
 assert(HAtomQuery:numerical_instantiation M atom witness member).
 { destruct(substitution_singleton_total M witness)as(ib&ic&HH&HT).
   exists ib,ic. split;[exact HH|].
   apply(proj2(numerical_substitution_member M(zeroM M)(succM M d)atom ib ic(code_numeral M 1)(zeroM M)member HAtom)).
   exists witness,d. exact(conj HH(conj(HT d)HMember)). }
 pose proof(source_whole_shift_instantiation M relative shiftedRelative k witness BRelative HRelativeShift)as HRelativeQuery.
 pose proof(source_instantiation_iff M atom shiftedRelative iff member relative result witness
   HIff HResult HAtomQuery HRelativeQuery)as HIffQuery.
 destruct(sf_relation_total M SFImpl envAt result)as(instance&HInstance).
 pose proof(source_instantiation_binary M SFImpl assignedEnv iff localbody witness envAt result instance
  (or_intror(or_intror eq_refl))HLocal HEnvQuery HIffQuery HInstance)as HQuery.
 pose proof(full_source_AllE M gb gc gn localbody point witness instance
  (source_wf_quantifier_instance M gb gc gn SFAll localbody point witness instance(or_introl eq_refl)
   HAll(source_full_prv_wellformed M gb gc gn point PPoint)HQuery)PPoint HAll HQuery)as PInstance.
 exact(source_full_modus_ponens M gb gc gn envAt result instance HInstance PInstance PEnv).
Qed.
Print Assumptions source_instantiation_iff.
Print Assumptions source_full_representation_query.
