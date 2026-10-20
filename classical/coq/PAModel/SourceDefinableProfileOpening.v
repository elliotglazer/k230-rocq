(** Exact opening of the canonical definability profile. The two actual
    binder instantiations cancel its two cutoff-one matrix insertions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SetSchemaConstructors SchemaConstructorBounds
 SourceBounded SourceFiniteCutoffShift SourceCutoffOpening SourceRepresentativeRenaming
 NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource
 SourcePropositionalRebase SourceIffGraphs SourceSetRelativization SourceSetRelativizationSubstitution
 SourceSetRelativizationFunctionality SourceLDefinableProfile.
Unset Implicit Arguments.

Theorem source_definable_profile_opening M domain phi m target body Y opened domainY allProfile profileBody x point assigned relative:
 source_bounded M phi(succM M m) ->source_definable_profile M domain phi target ->
 sf_relation M SFEx body(zeroM M)target ->numerical_instantiation M body Y opened ->
 sf_relation M SFAnd domainY allProfile opened ->sf_relation M SFAll profileBody(zeroM M)allProfile ->
 numerical_instantiation M profileBody x point ->source_representative_renaming M x phi assigned ->
 source_set_relativization M(zeroM M)assigned relative ->
 numerical_instantiation M domain Y domainY /\exists memberY memberA rhs,
 sf_relation M SFMember x Y memberY /\sf_relation M SFMember x(zeroM M)memberA /\
 sf_relation M SFAnd memberA relative rhs /\source_iff_graph M memberY rhs point.
Proof.
 intros HP(first&matrix&oldRel&HFirst&HMatrix&HOldRel&HRecipe)HEx
  (ib&ic&HHead&HOpened)HOpenedAnd HAll HInner HRep HRelative.
 set(rho:=L_definable_profile_environment oldRel domain).
 change(code_relation M rho(E_L_definable_profile(CEvar 0)(CEvar 1))target)in HRecipe.
 unfold E_L_definable_profile in HRecipe.
 destruct(schema_expression_split M rho SFEx _ _ target HRecipe)as(oldBody&z&HBody&HZ&HExOld).
 change(z=zeroM M)in HZ. subst z.
 destruct(sf_relation_injective M SFEx SFEx oldBody(zeroM M)body(zeroM M)target HExOld HEx)as(_&EBody&_). subst oldBody.
 destruct(schema_expression_split M rho SFAnd _ _ body HBody)as(oldDomain&oldAll&HDomain&HOldAll&HAndOld).
 change(oldDomain=domain)in HDomain. subst oldDomain.
 destruct(schema_expression_split M rho SFAll _ _ oldAll HOldAll)as(oldPoint&z&HOldPoint&HZ&HAllOld).
 change(z=zeroM M)in HZ. subst z.
 unfold E_sf_iff in HOldPoint.
 destruct(schema_expression_split M rho SFAnd _ _ oldPoint HOldPoint)as(lr&rl&HLR&HRL&HIffAnd).
 destruct(schema_expression_split M rho SFImpl _ _ lr HLR)as(my&rhs0&HMY&HRhs0&HForward).
 destruct(schema_expression_split M rho SFImpl _ _ rl HRL)as(rhs0'&my'&HRhs0'&HMY'&HBackward).
 assert(E:rhs0'=rhs0)by(eapply code_relation_functional;eassumption). subst rhs0'.
 assert(E:my'=my)by(eapply code_relation_functional;eassumption). subst my'.
 destruct(schema_expression_split M rho SFAnd _ _ rhs0 HRhs0)as(ma&r0&HMA&HR0&HRight0).
 change(r0=oldRel)in HR0. subst r0.
 assert(HMY0:sf_relation M SFMember(zeroM M)(code_numeral M 1)my).
 { exact(proj1(schema_expression_graph M rho SFMember(CEconst 0)(CEconst 1)(zeroM M)(code_numeral M 1)my eq_refl eq_refl)HMY). }
 assert(HMA0:sf_relation M SFMember(zeroM M)(code_numeral M 2)ma).
 { exact(proj1(schema_expression_graph M rho SFMember(CEconst 0)(CEconst 2)(zeroM M)(code_numeral M 2)ma eq_refl eq_refl)HMA). }
 pose proof(source_iff_build M my rhs0 lr rl oldPoint HForward HBackward HIffAnd)as HIff0.
 destruct(proj1(numerical_substitution_binary M SFAnd domain oldAll body ib ic(code_numeral M 1)(zeroM M)opened
  (or_introl eq_refl)HAndOld)HOpened)as(d1&all1&HDomain1&HAll1&HAnd1).
 destruct(sf_relation_injective M SFAnd SFAnd d1 all1 domainY allProfile opened HAnd1 HOpenedAnd)as(_&EDomain&EAll).
 change(all1=allProfile)in EAll. subst d1 all1.
 split;[exists ib,ic;auto|].
 destruct(proj1(numerical_substitution_quantifier M true oldPoint oldAll ib ic(code_numeral M 1)(zeroM M)allProfile HAllOld)HAll1)
  as(lb&lc&ln&p1&HLift&HPoint1&HAll1').
 destruct(sf_relation_injective M SFAll SFAll p1(zeroM M)profileBody(zeroM M)allProfile HAll1' HAll)as(_&EPoint&_).
 subst p1.
 pose proof(source_cutoff_shift_bounded M 1 phi first m HP HFirst)as BFirst.
 pose proof(source_cutoff_one_lifted_opening M first matrix(succM M(succM M m))ib ic lb lc ln BFirst HMatrix HLift)as HMatrixFirst.
 pose proof(proj2(substitution_lift_tail M ib ic(code_numeral M 1)(zeroM M)lb lc ln(code_numeral M 1)(zeroM M)HLift)
  (substitution_singleton_tail M ib ic(zeroM M)))as CarrierOuter.
 destruct(source_set_relativization_substitution_exists M matrix(code_numeral M 2)(code_numeral M 1)lb lc ln(code_numeral M 1)
  first oldRel CarrierOuter HMatrixFirst HOldRel)as(rel1&HRel1&HRelSub1).
 pose proof(proj1(proj2 HLift))as LiftZero.
 pose proof(proj2(substitution_lift_tail M ib ic(code_numeral M 1)(zeroM M)lb lc ln(zeroM M)Y HLift)HHead)as LiftY.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M Y))as(my1&HMY1).
 destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1))as(ma1&HMA1).
 assert(SMY1:numerical_substitution M my lb lc ln(code_numeral M 1)my1).
 { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 1)my lb lc ln(code_numeral M 1)my1 HMY0)).
   exists(zeroM M),(succM M Y). auto. }
 assert(SMA1:numerical_substitution M ma lb lc ln(code_numeral M 1)ma1).
 { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 2)ma lb lc ln(code_numeral M 1)ma1 HMA0)).
   exists(zeroM M),(code_numeral M 1). auto. }
 destruct(sf_relation_total M SFAnd ma1 rel1)as(rhs1&HRight1).
 assert(SRight1:numerical_substitution M rhs0 lb lc ln(code_numeral M 1)rhs1).
 { apply(proj2(numerical_substitution_binary M SFAnd ma oldRel rhs0 lb lc ln(code_numeral M 1)rhs1(or_introl eq_refl)HRight0)).
   exists ma1,rel1. auto. }
 destruct(source_iff_total M my1 rhs1)as(iff1&HIff1).
 pose proof(source_iff_substitution M my rhs0 oldPoint my1 rhs1 iff1 lb lc ln(code_numeral M 1)HIff0 HIff1 SMY1 SRight1)as SIff1.
 pose proof(numerical_substitution_functional M oldPoint lb lc ln(code_numeral M 1)profileBody iff1 HPoint1 SIff1)as E.
 subst profileBody.
 destruct HInner as(xb&xc&XHead&XSub).
 destruct(source_cutoff_one_open_representative M phi first x assigned(succM M m)HP HFirst HRep)as(fb&fc&FHead&FSub).
 assert(FirstAssigned:numerical_substitution M first xb xc(code_numeral M 1)(zeroM M)assigned).
 { exact(proj1(numerical_substitution_extensional M first fb fc(code_numeral M 1)xb xc(code_numeral M 1)(zeroM M)assigned
    (substitution_singletons_equivalent M fb fc xb xc x FHead XHead))FSub). }
 pose proof(substitution_singleton_tail M xb xc(zeroM M))as CarrierInner.
 destruct(source_set_relativization_substitution_exists M first(code_numeral M 1)(zeroM M)xb xc(code_numeral M 1)(zeroM M)
  assigned rel1 CarrierInner FirstAssigned HRel1)as(rel2&HRel2&HRelSub2).
 pose proof(source_set_relativization_functional M assigned(zeroM M)rel2 relative HRel2 HRelative)as E. subst rel2.
 destruct(sf_relation_total M SFMember x Y)as(memberY&HMemberY).
 destruct(sf_relation_total M SFMember x(zeroM M))as(memberA&HMemberA).
 assert(SMY2:numerical_substitution M my1 xb xc(code_numeral M 1)(zeroM M)memberY).
 { apply(proj2(numerical_substitution_member M(zeroM M)(succM M Y)my1 xb xc(code_numeral M 1)(zeroM M)memberY HMY1)).
   exists x,Y. split;[exact XHead|]. split;[apply substitution_singleton_tail|exact HMemberY]. }
 assert(SMA2:numerical_substitution M ma1 xb xc(code_numeral M 1)(zeroM M)memberA).
 { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 1)ma1 xb xc(code_numeral M 1)(zeroM M)memberA HMA1)).
   exists x,(zeroM M). auto. }
 destruct(sf_relation_total M SFAnd memberA relative)as(rhs&HRight).
 assert(SRight2:numerical_substitution M rhs1 xb xc(code_numeral M 1)(zeroM M)rhs).
 { apply(proj2(numerical_substitution_binary M SFAnd ma1 rel1 rhs1 xb xc(code_numeral M 1)(zeroM M)rhs(or_introl eq_refl)HRight1)).
   exists memberA,relative. auto. }
 destruct(source_iff_total M memberY rhs)as(final&HFinal).
 pose proof(source_iff_substitution M my1 rhs1 iff1 memberY rhs final xb xc(code_numeral M 1)(zeroM M)HIff1 HFinal SMY2 SRight2)as SFinal.
 pose proof(numerical_substitution_functional M iff1 xb xc(code_numeral M 1)(zeroM M)point final XSub SFinal)as E. subst final.
 exists memberY,memberA,rhs. auto.
Qed.
Print Assumptions source_definable_profile_opening.
