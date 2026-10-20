(** The actual first Dn step of a child representation recipe, retaining
    the arbitrary internal relative matrix while reopening its value/environment
    roles. This extends the checked EnvF head calibration through the iff. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SetCodeDescent SourceNumeralLift SourceBounded
 SourceDefinabilityPrimitives SourceDefinabilityStep SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierClosure
 SourceEnvironmentHeadCalibration SourceEnvironmentSuccessorHead SourceEnvFScopedHole SourceEnvironmentStepMaps SourceEnvironmentExtensionRotation
 SourceFiniteCutoffShift SourceQfFunctionality SourceCutoffQuantifiers SourceDnStep SourceRepresentationRecipe SourceIffGraphs
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming SchemaConstructorBounds SourceQuantifierChildRotation
 SourceQuantifierMatrixScopes SourceSetRelativization.
Unset Implicit Arguments.
Lemma source_iff_renaming M a b out a' b' out' rb rc rn delta:
 source_iff_graph M a b out ->source_iff_graph M a' b' out' ->
 numerical_renaming M a rb rc rn delta a' ->numerical_renaming M b rb rc rn delta b' ->
 numerical_renaming M out rb rc rn delta out'.
Proof.
 intros H H' HA HB. destruct(source_iff_parts M a b out H)as(lr&rl&HL&HR&HO).
 destruct(source_iff_parts M a' b' out' H')as(lr'&rl'&HL'&HR'&HO').
 apply(proj2(numerical_renaming_binary M SFAnd lr rl out rb rc rn delta out'(or_introl eq_refl)HO)).
 exists lr',rl'. split.
 - apply(proj2(numerical_renaming_binary M SFImpl a b lr rb rc rn delta lr'(or_intror(or_intror eq_refl))HL)).
   exists a',b'. auto.
 - split;[|exact HO']. apply(proj2(numerical_renaming_binary M SFImpl b a rl rb rc rn delta rl'
    (or_intror(or_intror eq_refl))HR)). exists b',a'. auto.
Qed.
Definition E_representation_head_point:=E_sf SFAll
 (E_sf SFImpl(CEconst(sf_make SFMember 0 2))
 (E_sf SFAll(E_sf SFImpl(E_sf SFEx(E_sf SFAnd(CEvar 0)(CEconst(sf_encode source_def_extension021)))(CEconst 0))
 (E_sf_iff(CEconst(sf_make SFMember 0 2))(CEvar 1)))(CEconst 0)))(CEconst 0).
Theorem source_representation_successor_head M count environment next firstnext guard f matrix relative point k:
 source_bounded M environment(succM M count) ->source_def_step M true environment next ->
 source_cutoff_shift M 1 next firstnext ->source_cutoff_shift M 1 firstnext guard ->
 source_bounded M f k ->
 numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 code_relation M(representation_point_environment guard relative)(E_representation_point(CEvar 0)(CEvar 1))point ->
 exists first deep child childrelative target,source_cutoff_shift M 1 environment first /\
 source_low_parameter_shift M 3 first deep /\source_quantifier_matrix M(code_numeral M 1)f child /\
 source_set_relativization M(code_numeral M 3)child childrelative /\
 code_relation M(representation_point_environment deep childrelative)E_representation_head_point target /\
 source_dn_successor M point target.
Proof.
 intros BF HStep HN1 HN2 BPhi HM HR HPoint.
 destruct(source_def_step_graph M true environment next HStep)as(shifted&pair&(first&HF1&HF2)&HPair&HNext).
 destruct(source_cutoff_quantifier_inv M 1 false pair next firstnext HNext HN1)as(pair1&HNext1&HShift1).
 destruct(source_cutoff_quantifier_inv M 1 false pair1 firstnext guard HNext1 HN2)as(pair2&HGuard&HShift2).
 destruct(environment_cutoff_binary_inv M 2 SFAnd shifted(code_numeral M(sf_encode source_def_extension021))pair pair1
  (or_introl eq_refl)HPair HShift1)as(shifted1&ext1&HS1&HE1&HPair1).
 destruct(environment_cutoff_binary_inv M 2 SFAnd shifted1 ext1 pair1 pair2
  (or_introl eq_refl)HPair1 HShift2)as(deep&ext2&HS2&HE2&HPair2).
 pose proof(source_low_parameter_shift_zero M environment(succM M count)BF)as HZero.
 pose proof(source_low_parameter_shift_step M 0 environment environment first(succM M count)BF HZero HF1)as HFirst.
 pose proof(source_low_parameter_shift_step M 1 environment first shifted(succM M count)BF HFirst HF2)as HSecond.
 pose proof(source_low_parameter_shift_cutoff_two M 1 environment shifted shifted1(succM M count)BF HSecond HS1)as HThird.
 pose proof(source_low_parameter_shift_cutoff_two M 2 environment shifted1 deep(succM M count)BF HThird HS2)as HDeep.
 pose proof(source_cutoff_shift_bounded M 1 environment first count BF HF1)as BFirst.
 pose proof(source_low_parameter_shift_zero M first(succM M(succM M count))BFirst)as HFirstZero.
 pose proof(source_low_parameter_shift_step M 0 first first shifted(succM M(succM M count))BFirst HFirstZero HF2)as HShift.
 pose proof(source_low_parameter_shift_cutoff_two M 0 first shifted shifted1(succM M(succM M count))BFirst HShift HS1)as HShiftLow1.
 pose proof(source_low_parameter_shift_cutoff_two M 1 first shifted1 deep(succM M(succM M count))BFirst HShiftLow1 HS2)as HShiftDeep.
 destruct(renaming_lift_total M(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M))as(b&c&n&HL1).
 destruct(renaming_lift_total M b c n(zeroM M))as(d&e&l&HL2).
 assert(HL:environment_rotation_lifts M b c n d e l)by(exact(conj HL1 HL2)).
 pose proof(source_low_four_rotation_invariant M environment deep(succM M count)b c n d e l BF HDeep HL)as HDeepFixed.
 pose proof(source_environment_extension_rotation M ext1 ext2 b c n d e l HE1 HE2 HL)as HExt.
 destruct(sf_relation_total M SFAnd deep(code_numeral M(sf_encode source_def_extension021)))as(deeppair&HDeepPair).
 assert(HPairMap:numerical_renaming M pair2 d e l(zeroM M)deeppair).
 { apply(proj2(numerical_renaming_binary M SFAnd deep ext2 pair2 d e l(zeroM M)deeppair(or_introl eq_refl)HPair2)).
   exists deep,(code_numeral M(sf_encode source_def_extension021)). exact(conj HDeepFixed(conj HExt HDeepPair)). }
 destruct(sf_relation_total M SFEx deeppair(zeroM M))as(ex&HEx).
 assert(HGuardMap:numerical_renaming M guard b c n(zeroM M)ex).
 { apply(proj2(numerical_renaming_quantifier M false pair2 guard b c n(zeroM M)ex HGuard)).
   exists d,e,l,deeppair. exact(conj HL2(conj HPairMap HEx)). }
 destruct(source_quantifier_child_relative_rotation M f matrix relative k b c n BPhi HL1 HM HR)
  as(child&childrelative&HChild&HChildRelative&HRelativeMap).
 destruct(code_relation_total M(E_sf SFMember(CEconst 0)(CEconst 1))(representation_point_environment guard relative))as(atom&HAtom).
 pose proof(proj1(schema_expression_graph M(representation_point_environment guard relative)SFMember(CEconst 0)(CEconst 1)
  (zeroM M)(code_numeral M 1)atom eq_refl eq_refl)HAtom)as HAtomGraph.
 destruct(source_iff_total M atom relative)as(iff&HIf).
 assert(HIfCode:code_relation M(representation_point_environment guard relative)
  (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1))iff).
 { destruct(source_iff_parts M atom relative iff HIf)as(lr&rl&HLR&HRL&HIff).
   unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HIff].
   - eapply environment_carrier_code_join;[exact HAtom|reflexivity|exact HLR].
   - eapply environment_carrier_code_join;[reflexivity|exact HAtom|exact HRL]. }
 destruct(code_relation_total M(E_sf SFImpl(CEvar 0)(E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1)))
  (representation_point_environment guard relative))as(body&HBody).
 pose proof(proj1(schema_expression_graph M(representation_point_environment guard relative)SFImpl(CEvar 0)_ guard iff body eq_refl HIfCode)HBody)as HBodyGraph.
 pose proof(proj1(schema_expression_graph M(representation_point_environment guard relative)SFAll _ (CEconst 0)body(zeroM M)point HBody eq_refl)HPoint)as HPointGraph.
 set(member:=code_numeral M(sf_make SFMember 0 2)).
 pose proof(sf_make_numeral M SFMember 0 2)as HMember.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 2)member)in HMember.
 assert(HAtomMap:numerical_renaming M atom b c n(zeroM M)member).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 1)atom b c n(zeroM M)member HAtomGraph)).
   exists(zeroM M),(code_numeral M 2). split.
   - exact(proj2(renaming_lift_head M _ _ _ _ b c n(zeroM M)HL1)eq_refl).
   - split;[|exact HMember]. exact(proj2(renaming_lift_tail M _ _ _ _ b c n(zeroM M)(code_numeral M 1)HL1)(source_dn_rotate_zero M)). }
 destruct(source_iff_total M member childrelative)as(newiff&HNewIf).
 pose proof(source_iff_renaming M atom relative iff member childrelative newiff b c n(zeroM M)
  HIf HNewIf HAtomMap HRelativeMap)as HIfMap.
 destruct(sf_relation_total M SFImpl ex newiff)as(localbody&HLocal).
 assert(HBodyMap:numerical_renaming M body b c n(zeroM M)localbody).
 { apply(proj2(numerical_renaming_binary M SFImpl guard iff body b c n(zeroM M)localbody(or_intror(or_intror eq_refl))HBodyGraph)).
   exists ex,newiff. exact(conj HGuardMap(conj HIfMap HLocal)). }
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(rotated&HRotated).
 assert(HPointMap:numerical_renaming M point(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)rotated).
 { apply(proj2(numerical_renaming_quantifier M true body point _ _ _ _ rotated HPointGraph)).
   exists b,c,n,localbody. exact(conj HL1(conj HBodyMap HRotated)). }
 destruct(sf_relation_total M SFImpl member rotated)as(headbody&HHead).
 destruct(sf_relation_total M SFAll headbody(zeroM M))as(target&HTarget).
 exists first,deep,child,childrelative,target. refine(conj HF1(conj HShiftDeep(conj HChild(conj HChildRelative(conj _ _))))).
 - assert(HNewIfCode:code_relation M(representation_point_environment deep childrelative)
    (E_sf_iff(CEconst(sf_make SFMember 0 2))(CEvar 1))newiff).
   { destruct(source_iff_parts M member childrelative newiff HNewIf)as(lr&rl&HLR&HRL&HIff).
     unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HIff].
     - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HLR].
     - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HRL]. }
   unfold E_representation_head_point.
   eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
   eapply environment_carrier_code_join;[reflexivity| |exact HHead].
   eapply environment_carrier_code_join;[|reflexivity|exact HRotated].
   eapply environment_carrier_code_join;[|exact HNewIfCode|exact HLocal].
   eapply environment_carrier_code_join;[|reflexivity|exact HEx].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HDeepPair].
 - exists rotated,member,headbody. exact(conj HPointMap(conj HMember(conj HHead HTarget))).
Qed.
Print Assumptions source_iff_renaming.
Print Assumptions source_representation_successor_head.
