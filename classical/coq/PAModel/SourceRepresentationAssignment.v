(** Literal numerical assignment of the representation point. The count,
    formula, and assignment vector are internal codes, possibly nonstandard.
    This removes all Dn guards by actual source derivations. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SetFormulaCodes SetSchemaConstructors SourceBounded NumericalEnvironments NumericalSubstitutionMaps
 NumericalSubstitution NumericalSourceFull SourceIffGraphs SourceEnvironmentCarrierClosure
 SourceRepresentationRecipe SourceRepresentationPointDataBound SourceRoleReopening
 SourceDefinabilityIteration SourceDefinabilityBounds SourceFiniteCutoffShift NumericalRenaming SourceSetRelativization SourceDn
 SourceDnAssignments SourceDnEliminationInvariant SourceDnElimination.
Unset Implicit Arguments.
Definition E_assigned_representation_point:=E_sf SFAll
 (E_sf SFImpl(CEvar 0)(E_sf_iff(E_sf SFMember(CEconst 0)(CEvar 2))(CEvar 1)))(CEconst 0).
Lemma source_representation_point_assignment M count d X pb pc ab ac lb lc ln
 environment relative body assignedEnv assignedRel point:
 source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 code_relation M(representation_point_environment environment relative)
  (E_representation_point(CEvar 0)(CEvar 1))body ->
 numerical_substitution M environment lb lc ln(code_numeral M 1)assignedEnv ->
 numerical_substitution M relative lb lc ln(code_numeral M 1)assignedRel ->
 code_relation M(schema_env3 assignedEnv assignedRel(succM M d))E_assigned_representation_point point ->
 numerical_substitution M body ab ac(succM M(succM M count))(zeroM M)point.
Proof.
 intros HA HL HB HE HR HP.
 destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1))as(atom&HAtom).
 destruct(source_iff_total M atom relative)as(iff&HIff).
 destruct(sf_relation_total M SFImpl environment iff)as(localbody&HLocal).
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(original&HOriginal).
 assert(HOriginalCode:code_relation M(representation_point_environment environment relative)
  (E_representation_point(CEvar 0)(CEvar 1))original).
 { unfold E_representation_point.
   eapply environment_carrier_code_join;[|reflexivity|exact HOriginal].
   eapply environment_carrier_code_join;[reflexivity| |exact HLocal].
   destruct(source_iff_parts M atom relative iff HIff)as(lr&rl&HLR&HRL&HAnd).
   unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HAnd].
   - eapply environment_carrier_code_join;[|reflexivity|exact HLR].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HAtom].
   - eapply environment_carrier_code_join;[reflexivity| |exact HRL].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HAtom]. }
 assert(EO:original=body)by(eapply code_relation_functional;eassumption). subst original.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M d))as(newatom&HNewAtom).
 destruct(source_iff_total M newatom assignedRel)as(newiff&HNewIff).
 destruct(sf_relation_total M SFImpl assignedEnv newiff)as(newlocal&HNewLocal).
 destruct(sf_relation_total M SFAll newlocal(zeroM M))as(target&HTarget).
 assert(HTargetCode:code_relation M(schema_env3 assignedEnv assignedRel(succM M d))
  E_assigned_representation_point target).
 { unfold E_assigned_representation_point.
   eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
   eapply environment_carrier_code_join;[reflexivity| |exact HNewLocal].
   destruct(source_iff_parts M newatom assignedRel newiff HNewIff)as(lr&rl&HLR&HRL&HAnd).
   unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HAnd].
   - eapply environment_carrier_code_join;[|reflexivity|exact HLR].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HNewAtom].
   - eapply environment_carrier_code_join;[reflexivity| |exact HRL].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HNewAtom]. }
 assert(ET:target=point)by(eapply code_relation_functional;eassumption). subst target.
 assert(HAtomMap:numerical_substitution M atom lb lc ln(code_numeral M 1)newatom).
 { apply(proj2(numerical_substitution_member M _ _ atom lb lc ln(code_numeral M 1)newatom HAtom)).
   exists(zeroM M),(succM M d). split.
   - exact(proj2(substitution_lift_head M _ _ _ _ _ _ _ _ HL)eq_refl).
   - split;[|exact HNewAtom].
     apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
     exact(source_dn_assignment_zero M _ _ _ _ _ _ _ HA). }
 pose proof(source_iff_substitution M atom relative iff newatom assignedRel newiff lb lc ln
  (code_numeral M 1)HIff HNewIff HAtomMap HR)as HIffMap.
 assert(HLocalMap:numerical_substitution M localbody lb lc ln(code_numeral M 1)newlocal).
 { apply(proj2(numerical_substitution_binary M SFImpl environment iff localbody lb lc ln
    (code_numeral M 1)newlocal(or_intror(or_intror eq_refl))HLocal)).
   exists assignedEnv,newiff. exact(conj HE(conj HIffMap HNewLocal)). }
 apply(proj2(numerical_substitution_quantifier M true localbody body ab ac
  (succM M(succM M count))(zeroM M)point HOriginal)).
 exists lb,lc,ln,newlocal. exact(conj HL(conj HLocalMap HTarget)).
Qed.
Theorem source_full_representation_assignment M count phi rep d X rb rc assignedRep
 pb pc ab ac lb lc ln environment first shifted matrix relative body assignedEnv assignedRel point gb gc gn:
 source_bounded M phi count ->source_envf M count environment ->
 source_cutoff_shift M 1 environment first ->source_cutoff_shift M 1 first shifted ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 code_relation M(representation_point_environment shifted relative)
  (E_representation_point(CEvar 0)(CEvar 1))body ->source_dn M count body rep ->
 source_role_reopening M X d rb rc ->
 numerical_substitution M rep rb rc(code_numeral M 2)(code_numeral M 2)assignedRep ->
 source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 numerical_substitution M shifted lb lc ln(code_numeral M 1)assignedEnv ->
 numerical_substitution M relative lb lc ln(code_numeral M 1)assignedRel ->
 code_relation M(schema_env3 assignedEnv assignedRel(succM M d))E_assigned_representation_point point ->
 source_full_prv M gb gc gn assignedRep ->source_dn_parameter_proofs M count pb pc X gb gc gn ->
 source_full_prv M gb gc gn point.
Proof.
 intros BF HE H1 H2 HM HR HB HD HOpen HRep HA HL HEnv HRel HPoint PRep HMembers.
 eapply source_full_dn_elimination with(body:=body)(dn:=rep)(d:=d)(X:=X)(rb:=rb)(rc:=rc)
  (pc:=assignedRep)(pb:=pb)(pC:=pc)(ab:=ab)(ac:=ac).
 - exact(source_representation_point_data_bound M count phi environment first shifted matrix relative body
    BF HE H1 H2 HM HR HB).
 - exact HD.
 - exact HOpen.
 - exact HRep.
 - exact HA.
 - exact(source_representation_point_assignment M count d X pb pc ab ac lb lc ln shifted relative body
    assignedEnv assignedRel point HA HL HB HEnv HRel HPoint).
 - exact PRep.
 - exact HMembers.
Qed.
Print Assumptions source_representation_point_assignment.
Print Assumptions source_full_representation_assignment.
