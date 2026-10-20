(** Identify the actual EnvF-successor/Dn head with the finite named
 head template. This is a constructor and renaming proof for arbitrary codes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceNumeralLift SourceBounded
 SourceDefinabilityPrimitives SourceDefinabilityStep SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierClosure
 SourceEnvironmentHeadCalibration SourceEnvFScopedHole SourceEnvironmentStepMaps SourceEnvironmentExtensionRotation
 SourceFiniteCutoffShift SourceQfFunctionality SourceCutoffQuantifiers SourceDnStep
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming SchemaConstructorBounds.
Unset Implicit Arguments.
Lemma environment_cutoff_binary_inv M depth h a b source target:
 sf_binary h ->sf_relation M h a b source ->source_cutoff_shift M depth source target ->
 exists a' b',source_cutoff_shift M depth a a' /\source_cutoff_shift M depth b b' /\sf_relation M h a' b' target.
Proof.
 intros HH HSource(x&y&l&HMap&HSub).
 destruct(proj1(numerical_substitution_binary M h a b source x y l(code_numeral M(S depth))target HH HSource)HSub)
  as(a'&b'&HA&HB&HT).
 exists a',b'. exact(conj(ex_intro _ x(ex_intro _ y(ex_intro _ l(conj HMap HA))))
  (conj(ex_intro _ x(ex_intro _ y(ex_intro _ l(conj HMap HB))))HT)).
Qed.
Theorem source_environment_successor_head M count environment next firstnext guard point:
 source_bounded M environment(succM M count) ->source_def_step M true environment next ->
 source_cutoff_shift M 1 next firstnext ->source_cutoff_shift M 1 firstnext guard ->
 code_relation M(fun _=>guard)E_environment_carrier_point point ->
 exists first deep target,source_cutoff_shift M 1 environment first /\
 source_low_parameter_shift M 3 first deep /\
 code_relation M(fun _=>deep)E_environment_head_point target /\source_dn_successor M point target.
Proof.
 intros BF HStep HN1 HN2 HPoint.
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
 destruct(code_relation_total M(E_sf SFMember(CEconst 0)(CEconst 1))(fun _=>guard))as(atom&HAtom).
 pose proof(proj1(schema_expression_graph M(fun _=>guard)SFMember(CEconst 0)(CEconst 1)
  (zeroM M)(code_numeral M 1)atom eq_refl eq_refl)HAtom)as HAtomGraph.
 destruct(code_relation_total M(E_sf SFImpl(CEvar 0)(E_sf SFMember(CEconst 0)(CEconst 1)))(fun _=>guard))as(body&HBody).
 pose proof(proj1(schema_expression_graph M(fun _=>guard)SFImpl(CEvar 0)_ guard atom body eq_refl HAtom)HBody)as HBodyGraph.
 pose proof(proj1(schema_expression_graph M(fun _=>guard)SFAll _ (CEconst 0)body(zeroM M)point HBody eq_refl)HPoint)as HPointGraph.
 set(member:=code_numeral M(sf_make SFMember 0 2)).
 pose proof(sf_make_numeral M SFMember 0 2)as HMember.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 2)member)in HMember.
 assert(HAtomMap:numerical_renaming M atom b c n(zeroM M)member).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 1)atom b c n(zeroM M)member HAtomGraph)).
   exists(zeroM M),(code_numeral M 2). split.
   - exact(proj2(renaming_lift_head M _ _ _ _ b c n(zeroM M)HL1)eq_refl).
   - split;[|exact HMember]. exact(proj2(renaming_lift_tail M _ _ _ _ b c n(zeroM M)(code_numeral M 1)HL1)(source_dn_rotate_zero M)). }
 destruct(sf_relation_total M SFImpl ex member)as(localbody&HLocal).
 assert(HBodyMap:numerical_renaming M body b c n(zeroM M)localbody).
 { apply(proj2(numerical_renaming_binary M SFImpl guard atom body b c n(zeroM M)localbody(or_intror(or_intror eq_refl))HBodyGraph)).
   exists ex,member. exact(conj HGuardMap(conj HAtomMap HLocal)). }
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(rotated&HRotated).
 assert(HPointMap:numerical_renaming M point(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)rotated).
 { apply(proj2(numerical_renaming_quantifier M true body point _ _ _ _ rotated HPointGraph)).
   exists b,c,n,localbody. exact(conj HL1(conj HBodyMap HRotated)). }
 destruct(sf_relation_total M SFImpl member rotated)as(headbody&HHead).
 destruct(sf_relation_total M SFAll headbody(zeroM M))as(target&HTarget).
 exists first,deep,target. refine(conj HF1(conj HShiftDeep(conj _ _))).
 - unfold E_environment_head_point.
   eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
   eapply environment_carrier_code_join;[reflexivity| |exact HHead].
   eapply environment_carrier_code_join;[|reflexivity|exact HRotated].
   eapply environment_carrier_code_join;[|reflexivity|exact HLocal].
   eapply environment_carrier_code_join;[|reflexivity|exact HEx].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HDeepPair].
 - exists rotated,member,headbody. exact(conj HPointMap(conj HMember(conj HHead HTarget))).
Qed.
Print Assumptions source_environment_successor_head.
