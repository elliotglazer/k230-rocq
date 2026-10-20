(** Rename only the child representative in the actual first-Dn head.
    Environment and relative matrix invariance are proved by arithmetic maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent SetSchemaConstructors SchemaConstructorBounds
 SourceNumeralLift SourceBounded SourceRenamingIdentity NumericalRenamingMaps NumericalRenaming SourceRepresentativeRenaming
 SourceProjectionRepresentativeMaps SourceQuantifierMatrixScopes SourceSetRelativization SourceEnvironmentHeadCalibration SourceRepresentationSuccessorHead
 SourceRepresentationRecipe SourceEnvironmentCarrierClosure SourceDefinabilityPrimitives SourceEnvFScopedHole SourceIffGraphs SourceNamedFiniteCalibration.
Unset Implicit Arguments.
Definition E_projection_child_head_point:=E_sf SFAll
 (E_sf SFImpl(CEconst(sf_make SFMember 0 2))
 (E_sf SFAll(E_sf SFImpl(E_sf SFEx(E_sf SFAnd(CEvar 0)(CEconst(sf_encode source_def_extension021)))(CEconst 0))
 (E_sf_iff(E_sf SFMember(CEconst 0)(CEvar 2))(CEvar 1)))(CEconst 0)))(CEconst 0).
Theorem source_projection_head_representative_image M first deep f child relative original renamed k q r:
 source_bounded M first k ->source_low_parameter_shift M 3 first deep ->
 source_bounded M f q ->source_quantifier_matrix M(code_numeral M 1)f child ->
 source_set_relativization M(code_numeral M 3)child relative ->
 code_relation M(representation_point_environment deep relative)E_representation_head_point original ->
 code_relation M(schema_env3 deep relative(succM M(succM M r)))E_projection_child_head_point renamed ->
 source_representative_renaming M r original renamed.
Proof.
 intros BF HD BP HC HR HO HN.
 destruct(renaming_lift_total M r r(code_numeral M 1)(zeroM M))as(b&c&n&HL1).
 destruct(renaming_lift_total M b c n(zeroM M))as(d&e&l&HL2).
 destruct(renaming_lift_total M d e l(zeroM M))as(u&v&m&HL3).
 assert(HL:projection_representative_lifts M r b c n d e l u v m)by(exact(conj HL1(conj HL2 HL3))).
 pose proof(projection_representative_fixes_environment M first deep k r b c n d e l u v m BF HD HL)as HDeep.
 pose proof(projection_representative_fixes_child_relative M f child relative q r b c n d e l BP HC HR HL1 HL2)as HRel.
 set(atom:=code_numeral M(sf_make SFMember 0 2)).
 set(ext:=code_numeral M(sf_encode source_def_extension021)).
 pose proof(sf_make_numeral M SFMember 0 2)as HAtom.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 2)atom)in HAtom.
 assert(HExt:numerical_renaming M ext u v m(zeroM M)ext).
 { apply(numerical_renaming_identity_on_bound M ext u v m(zeroM M)(code_numeral M 3)(numerical_def_extension_bound M)).
   intros i HI. apply(projection_representative_three_fixed M r b c n d e l u v m i HL).
   intro E. rewrite E in HI. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)
    (code_numeral M 3)(code_numeral M 3)HI eq_refl). }
 destruct(sf_relation_total M SFAnd deep ext)as(pair&HPair).
 destruct(sf_relation_total M SFEx pair(zeroM M))as(guard&HGuard).
 assert(HPairMap:numerical_renaming M pair u v m(zeroM M)pair).
 { apply(proj2(numerical_renaming_binary M SFAnd deep ext pair u v m(zeroM M)pair(or_introl eq_refl)HPair)).
   exists deep,ext. exact(conj HDeep(conj HExt HPair)). }
 assert(HGuardMap:numerical_renaming M guard d e l(zeroM M)guard).
 { apply(proj2(numerical_renaming_quantifier M false pair guard d e l(zeroM M)guard HGuard)).
   exists u,v,m,pair. exact(conj HL3(conj HPairMap HGuard)). }
 destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M r)))as(newatom&HNewAtom).
 assert(HAtom2:numerical_renaming M atom d e l(zeroM M)newatom).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2)atom d e l(zeroM M)newatom HAtom)).
   exists(zeroM M),(succM M(succM M r)). split.
   - apply(projection_representative_two_fixed M r b c n d e l(zeroM M)HL1 HL2(source_fixed_numeral_neq M 0 2 ltac:(discriminate))).
   - exact(conj(projection_representative_two_changed M r b c n d e l HL1 HL2)HNewAtom). }
 assert(HAtom1:numerical_renaming M atom b c n(zeroM M)atom).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2)atom b c n(zeroM M)atom HAtom)).
   exists(zeroM M),(code_numeral M 2). split.
   - exact(proj2(renaming_lift_head M _ _ _ _ b c n(zeroM M)HL1)eq_refl).
   - exact(conj(representative_lift_fixed M r b c n(code_numeral M 2)HL1(source_fixed_numeral_neq M 2 1 ltac:(discriminate)))HAtom). }
 destruct(source_iff_total M atom relative)as(oldiff&HOldIff).
 destruct(source_iff_total M newatom relative)as(newiff&HNewIff).
 pose proof(source_iff_renaming M atom relative oldiff newatom relative newiff d e l(zeroM M)HOldIff HNewIff HAtom2 HRel)as HIffMap.
 destruct(sf_relation_total M SFImpl guard oldiff)as(oldlocal&HOldLocal).
 destruct(sf_relation_total M SFImpl guard newiff)as(newlocal&HNewLocal).
 assert(HLocalMap:numerical_renaming M oldlocal d e l(zeroM M)newlocal).
 { apply(proj2(numerical_renaming_binary M SFImpl guard oldiff oldlocal d e l(zeroM M)newlocal(or_intror(or_intror eq_refl))HOldLocal)).
   exists guard,newiff. exact(conj HGuardMap(conj HIffMap HNewLocal)). }
 destruct(sf_relation_total M SFAll oldlocal(zeroM M))as(oldall&HOldAll).
 destruct(sf_relation_total M SFAll newlocal(zeroM M))as(newall&HNewAll).
 assert(HAllMap:numerical_renaming M oldall b c n(zeroM M)newall).
 { apply(proj2(numerical_renaming_quantifier M true oldlocal oldall b c n(zeroM M)newall HOldAll)).
   exists d,e,l,newlocal. exact(conj HL2(conj HLocalMap HNewAll)). }
 destruct(sf_relation_total M SFImpl atom oldall)as(oldbody&HOldBody).
 destruct(sf_relation_total M SFImpl atom newall)as(newbody&HNewBody).
 assert(HBodyMap:numerical_renaming M oldbody b c n(zeroM M)newbody).
 { apply(proj2(numerical_renaming_binary M SFImpl atom oldall oldbody b c n(zeroM M)newbody(or_intror(or_intror eq_refl))HOldBody)).
   exists atom,newall. exact(conj HAtom1(conj HAllMap HNewBody)). }
 destruct(sf_relation_total M SFAll oldbody(zeroM M))as(oldhead&HOldHead).
 destruct(sf_relation_total M SFAll newbody(zeroM M))as(newhead&HNewHead).
 assert(HOldCode:code_relation M(representation_point_environment deep relative)E_representation_head_point oldhead).
 { destruct(source_iff_parts M atom relative oldiff HOldIff)as(lr&rl&HLR&HRL&HAnd).
   assert(GI:code_relation M(representation_point_environment deep relative)
    (E_sf_iff(CEconst(sf_make SFMember 0 2))(CEvar 1))oldiff).
   { unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HAnd].
     - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HLR].
     - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HRL]. }
   unfold E_representation_head_point. eapply environment_carrier_code_join;[|reflexivity|exact HOldHead].
   eapply environment_carrier_code_join;[reflexivity| |exact HOldBody].
   eapply environment_carrier_code_join;[|reflexivity|exact HOldAll].
   eapply environment_carrier_code_join;[|exact GI|exact HOldLocal].
   eapply environment_carrier_code_join;[|reflexivity|exact HGuard].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPair]. }
 assert(HNewCode:code_relation M(schema_env3 deep relative(succM M(succM M r)))E_projection_child_head_point newhead).
 { destruct(source_iff_parts M newatom relative newiff HNewIff)as(lr&rl&HLR&HRL&HAnd).
   assert(GA:code_relation M(schema_env3 deep relative(succM M(succM M r)))(E_sf SFMember(CEconst 0)(CEvar 2))newatom).
   { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HNewAtom]. }
   assert(GI:code_relation M(schema_env3 deep relative(succM M(succM M r)))
    (E_sf_iff(E_sf SFMember(CEconst 0)(CEvar 2))(CEvar 1))newiff).
   { unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HAnd].
     - eapply environment_carrier_code_join;[exact GA|reflexivity|exact HLR].
     - eapply environment_carrier_code_join;[reflexivity|exact GA|exact HRL]. }
   unfold E_projection_child_head_point. eapply environment_carrier_code_join;[|reflexivity|exact HNewHead].
   eapply environment_carrier_code_join;[reflexivity| |exact HNewBody].
   eapply environment_carrier_code_join;[|reflexivity|exact HNewAll].
   eapply environment_carrier_code_join;[|exact GI|exact HNewLocal].
   eapply environment_carrier_code_join;[|reflexivity|exact HGuard].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPair]. }
 assert(EO:oldhead=original)by(eapply code_relation_functional;eassumption). subst oldhead.
 assert(EN:newhead=renamed)by(eapply code_relation_functional;eassumption). subst newhead.
 apply(proj2(numerical_renaming_quantifier M true oldbody original r r(code_numeral M 1)(zeroM M)renamed HOldHead)).
 exists b,c,n,newbody. exact(conj HL1(conj HBodyMap HNewHead)).
Qed.
Print Assumptions source_projection_head_representative_image.
