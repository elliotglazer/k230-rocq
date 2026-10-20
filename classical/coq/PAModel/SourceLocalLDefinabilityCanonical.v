(** Uniform canonical local L-definability from actual representation,
    environment and fixed Def proofs. Every auxiliary role is allocated
    deterministically above the included context and original parameters. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes NumericalProofs
 SourceBounded SourceBoundMonotone SourceFiniteFamilyBounds NumericalContexts NumericalSourceFull
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceDefinabilityBounds SourceDefinabilityStep SourceDefinabilityIteration
 SourceEnvInClosureRecipe SourceRoleReopening SourceDnEliminationInvariant SourceBallSMembershipBlock SourceCanonicalParameterAssignment
 SourceSetRelativization SourceLDefinableProfile SourceOrdinalPredicate SourceHierarchySyntax SourceLFixed SourceNamedQuantifierRules SourceNamedVacuity SourceNamedElimination
 SourceIffGraphs SourceFiniteParameters SourceFiniteParameterProofs SourceFiniteNameParameters SourceParameterGraphs SourceParameterVacuity SourceDefinabilityPrimitives
 SourceLocalLDefinabilityExistsFromData SourceLocalCanonicalProfileOpening SourceLocalPrefixProperties SourceLocalGeneratorFacts SourceLocalFiniteBounds
 SourceLocalDefinabilityContext SourceLocalDefinabilityUnpack SourceLocalDefinabilityContent SourceLocalDefinabilityAccess
 SourceLocalSelectedSubset SourceLocalNamedClosureExistence SourceLocalSelectionExistsGraph SourceSelectionSCBinder SourceSelectionOperationGraph
 SourceEnvInClosureConstructor SourceEnvironmentCarrierClosure SourceThreeParameterCommutation SourceDerivedRules.
From Undecidability.FOL Require Import Syntax.Bounded.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Lia Arith.PeanoNat.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_bounded source_named_quantifier source_set_relativization numerical_substitution numerical_instantiation code_relation.
Theorem source_full_local_L_definability_canonical M count phi repClosure environment envClosure fb fc fn gb gc gn contextBound
 ordinalName ordinal level Ltarget:
 source_bounded M phi(succM M count) ->source_representation_in_closure_recipe M(succM M count)phi repClosure ->
 source_envf M count environment ->source_env_in_closure_recipe M count environment envClosure ->
 source_local_fixed_context M fb fc fn ->source_full_prv M fb fc fn repClosure ->source_full_prv M fb fc fn envClosure ->
 context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn contextBound ->
 numerical_instantiation M(source_ordinal_predicate_code M)ordinalName ordinal ->source_LL_instance M ordinalName(zeroM M)level ->
 source_full_prv M gb gc gn ordinal ->source_full_prv M gb gc gn level ->
 (forall i member,coding_lt M i count ->sf_relation M SFMember(succM M i)(zeroM M)member ->source_full_prv M gb gc gn member) ->
 source_L_definable_profile M phi Ltarget ->source_full_prv M gb gc gn Ltarget.
Proof.
 intros BF HRepClosure HE HEnvClosure HFixed PRepClosure PEnvClosure HIncluded BContext HOrdinal HLevel POrdinal PLevel HParameters HLtarget.
 destruct(source_finite_names_bound M(contextBound::succM M count::nil))as(base&HBase).
 assert(BCBase:coding_lt M contextBound base)by(exact(HBase contextBound(or_introl eq_refl))).
 assert(BCountBase:coding_lt M(succM M count)base)by(exact(HBase(succM M count)(or_intror(or_introl eq_refl)))).
 set(selected:=source_local_high_name M base 0).
 set(definables:=source_local_high_name M base 1).
 set(successor:=source_local_high_name M base 2).
 set(closure:=source_local_high_name M base 3).
 set(d:=source_local_high_name M base 4).
 set(old:=source_local_high_name M base 5).
 set(value:=source_local_high_name M base 6).
 set(new:=source_local_high_name M base 7).
 set(k:=source_local_high_name M base 8).
 assert(L0:coding_lt M selected(succM M selected))by apply coding_lt_succ.
 assert(BN0:coding_lt M selected k)by(exact(source_local_high_name_order M base 0 8 ltac:(lia))).
 assert(CN0:coding_lt M(succM M count)(succM M selected))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 0))).
 assert(GN0:coding_lt M contextBound(succM M selected))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 0))).
 assert(ZN0:zeroM M<>selected).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN0)). }
 assert(L1:coding_lt M definables(succM M definables))by apply coding_lt_succ.
 assert(BN1:coding_lt M definables k)by(exact(source_local_high_name_order M base 1 8 ltac:(lia))).
 assert(CN1:coding_lt M(succM M count)(succM M definables))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 1))).
 assert(GN1:coding_lt M contextBound(succM M definables))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 1))).
 assert(ZN1:zeroM M<>definables).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN1)). }
 assert(L2:coding_lt M successor(succM M successor))by apply coding_lt_succ.
 assert(BN2:coding_lt M successor k)by(exact(source_local_high_name_order M base 2 8 ltac:(lia))).
 assert(CN2:coding_lt M(succM M count)(succM M successor))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 2))).
 assert(GN2:coding_lt M contextBound(succM M successor))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 2))).
 assert(ZN2:zeroM M<>successor).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN2)). }
 assert(L3:coding_lt M closure(succM M closure))by apply coding_lt_succ.
 assert(BN3:coding_lt M closure k)by(exact(source_local_high_name_order M base 3 8 ltac:(lia))).
 assert(CN3:coding_lt M(succM M count)(succM M closure))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 3))).
 assert(GN3:coding_lt M contextBound(succM M closure))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 3))).
 assert(ZN3:zeroM M<>closure).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN3)). }
 assert(L4:coding_lt M d(succM M d))by apply coding_lt_succ.
 assert(BN4:coding_lt M d k)by(exact(source_local_high_name_order M base 4 8 ltac:(lia))).
 assert(CN4:coding_lt M(succM M count)(succM M d))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 4))).
 assert(GN4:coding_lt M contextBound(succM M d))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 4))).
 assert(ZN4:zeroM M<>d).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN4)). }
 assert(L5:coding_lt M old(succM M old))by apply coding_lt_succ.
 assert(BN5:coding_lt M old k)by(exact(source_local_high_name_order M base 5 8 ltac:(lia))).
 assert(CN5:coding_lt M(succM M count)(succM M old))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 5))).
 assert(GN5:coding_lt M contextBound(succM M old))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 5))).
 assert(ZN5:zeroM M<>old).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN5)). }
 assert(L6:coding_lt M value(succM M value))by apply coding_lt_succ.
 assert(BN6:coding_lt M value k)by(exact(source_local_high_name_order M base 6 8 ltac:(lia))).
 assert(CN6:coding_lt M(succM M count)(succM M value))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 6))).
 assert(GN6:coding_lt M contextBound(succM M value))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 6))).
 assert(ZN6:zeroM M<>value).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN6)). }
 assert(L7:coding_lt M new(succM M new))by apply coding_lt_succ.
 assert(BN7:coding_lt M new k)by(exact(source_local_high_name_order M base 7 8 ltac:(lia))).
 assert(CN7:coding_lt M(succM M count)(succM M new))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 7))).
 assert(GN7:coding_lt M contextBound(succM M new))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 7))).
 assert(ZN7:zeroM M<>new).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN7)). }
 assert(L8:coding_lt M k(succM M k))by apply coding_lt_succ.
 assert(CN8:coding_lt M(succM M count)(succM M k))by(exact(coding_lt_trans M _ _ _ BCountBase(source_local_high_name_above M base 8))).
 assert(GN8:coding_lt M contextBound(succM M k))by(exact(coding_lt_trans M _ _ _ BCBase(source_local_high_name_above M base 8))).
 assert(ZN8:zeroM M<>k).
 { exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN8)). }
 assert(N01:selected<>definables)by(exact(source_local_high_name_distinct M base 0 1 ltac:(lia))).
 assert(N02:selected<>successor)by(exact(source_local_high_name_distinct M base 0 2 ltac:(lia))).
 assert(N03:selected<>closure)by(exact(source_local_high_name_distinct M base 0 3 ltac:(lia))).
 assert(N04:selected<>d)by(exact(source_local_high_name_distinct M base 0 4 ltac:(lia))).
 assert(N05:selected<>old)by(exact(source_local_high_name_distinct M base 0 5 ltac:(lia))).
 assert(N06:selected<>value)by(exact(source_local_high_name_distinct M base 0 6 ltac:(lia))).
 assert(N07:selected<>new)by(exact(source_local_high_name_distinct M base 0 7 ltac:(lia))).
 assert(N10:definables<>selected)by(exact(source_local_high_name_distinct M base 1 0 ltac:(lia))).
 assert(N12:definables<>successor)by(exact(source_local_high_name_distinct M base 1 2 ltac:(lia))).
 assert(N13:definables<>closure)by(exact(source_local_high_name_distinct M base 1 3 ltac:(lia))).
 assert(N14:definables<>d)by(exact(source_local_high_name_distinct M base 1 4 ltac:(lia))).
 assert(N15:definables<>old)by(exact(source_local_high_name_distinct M base 1 5 ltac:(lia))).
 assert(N16:definables<>value)by(exact(source_local_high_name_distinct M base 1 6 ltac:(lia))).
 assert(N17:definables<>new)by(exact(source_local_high_name_distinct M base 1 7 ltac:(lia))).
 assert(N20:successor<>selected)by(exact(source_local_high_name_distinct M base 2 0 ltac:(lia))).
 assert(N21:successor<>definables)by(exact(source_local_high_name_distinct M base 2 1 ltac:(lia))).
 assert(N23:successor<>closure)by(exact(source_local_high_name_distinct M base 2 3 ltac:(lia))).
 assert(N24:successor<>d)by(exact(source_local_high_name_distinct M base 2 4 ltac:(lia))).
 assert(N25:successor<>old)by(exact(source_local_high_name_distinct M base 2 5 ltac:(lia))).
 assert(N26:successor<>value)by(exact(source_local_high_name_distinct M base 2 6 ltac:(lia))).
 assert(N27:successor<>new)by(exact(source_local_high_name_distinct M base 2 7 ltac:(lia))).
 assert(N30:closure<>selected)by(exact(source_local_high_name_distinct M base 3 0 ltac:(lia))).
 assert(N31:closure<>definables)by(exact(source_local_high_name_distinct M base 3 1 ltac:(lia))).
 assert(N32:closure<>successor)by(exact(source_local_high_name_distinct M base 3 2 ltac:(lia))).
 assert(N34:closure<>d)by(exact(source_local_high_name_distinct M base 3 4 ltac:(lia))).
 assert(N35:closure<>old)by(exact(source_local_high_name_distinct M base 3 5 ltac:(lia))).
 assert(N36:closure<>value)by(exact(source_local_high_name_distinct M base 3 6 ltac:(lia))).
 assert(N37:closure<>new)by(exact(source_local_high_name_distinct M base 3 7 ltac:(lia))).
 assert(N40:d<>selected)by(exact(source_local_high_name_distinct M base 4 0 ltac:(lia))).
 assert(N41:d<>definables)by(exact(source_local_high_name_distinct M base 4 1 ltac:(lia))).
 assert(N42:d<>successor)by(exact(source_local_high_name_distinct M base 4 2 ltac:(lia))).
 assert(N43:d<>closure)by(exact(source_local_high_name_distinct M base 4 3 ltac:(lia))).
 assert(N45:d<>old)by(exact(source_local_high_name_distinct M base 4 5 ltac:(lia))).
 assert(N46:d<>value)by(exact(source_local_high_name_distinct M base 4 6 ltac:(lia))).
 assert(N47:d<>new)by(exact(source_local_high_name_distinct M base 4 7 ltac:(lia))).
 assert(N50:old<>selected)by(exact(source_local_high_name_distinct M base 5 0 ltac:(lia))).
 assert(N51:old<>definables)by(exact(source_local_high_name_distinct M base 5 1 ltac:(lia))).
 assert(N52:old<>successor)by(exact(source_local_high_name_distinct M base 5 2 ltac:(lia))).
 assert(N53:old<>closure)by(exact(source_local_high_name_distinct M base 5 3 ltac:(lia))).
 assert(N54:old<>d)by(exact(source_local_high_name_distinct M base 5 4 ltac:(lia))).
 assert(N56:old<>value)by(exact(source_local_high_name_distinct M base 5 6 ltac:(lia))).
 assert(N57:old<>new)by(exact(source_local_high_name_distinct M base 5 7 ltac:(lia))).
 assert(N60:value<>selected)by(exact(source_local_high_name_distinct M base 6 0 ltac:(lia))).
 assert(N61:value<>definables)by(exact(source_local_high_name_distinct M base 6 1 ltac:(lia))).
 assert(N62:value<>successor)by(exact(source_local_high_name_distinct M base 6 2 ltac:(lia))).
 assert(N63:value<>closure)by(exact(source_local_high_name_distinct M base 6 3 ltac:(lia))).
 assert(N64:value<>d)by(exact(source_local_high_name_distinct M base 6 4 ltac:(lia))).
 assert(N65:value<>old)by(exact(source_local_high_name_distinct M base 6 5 ltac:(lia))).
 assert(N67:value<>new)by(exact(source_local_high_name_distinct M base 6 7 ltac:(lia))).
 assert(N70:new<>selected)by(exact(source_local_high_name_distinct M base 7 0 ltac:(lia))).
 assert(N71:new<>definables)by(exact(source_local_high_name_distinct M base 7 1 ltac:(lia))).
 assert(N72:new<>successor)by(exact(source_local_high_name_distinct M base 7 2 ltac:(lia))).
 assert(N73:new<>closure)by(exact(source_local_high_name_distinct M base 7 3 ltac:(lia))).
 assert(N74:new<>d)by(exact(source_local_high_name_distinct M base 7 4 ltac:(lia))).
 assert(N75:new<>old)by(exact(source_local_high_name_distinct M base 7 5 ltac:(lia))).
 assert(N76:new<>value)by(exact(source_local_high_name_distinct M base 7 6 ltac:(lia))).

 assert(BCK:context_bounded M gb gc gn k).
 { intros f HF. exact(source_bounded_monotone M f contextBound k(BContext f HF)GN8). }
 pose proof HRepClosure as HRC. destruct HRC as(rep&s0&c0&tb&te&tm&HRep&_).
 pose proof(source_representation_recipe_bounded M(succM M count)phi rep BF HRep)as BRep.
 destruct(source_role_reopening_total M(zeroM M)d)as(rb&rc&HOpen).
 destruct(numerical_substitution_total M rep rb rc(code_numeral M 2)(code_numeral M 2))as(assignedRep&HAssignedRep).
 pose proof(source_local_assigned_representation_bound M rep(zeroM M)d rb rc assignedRep k BRep HOpen HAssignedRep
  (source_bound_lt_le M _ _ _ (coding_zero_lt_succ M count)CN8)BN4)as BAssignedRep.
 destruct(source_def_step_total M true environment)as(next&HStep).
 assert(HNext:source_envf M(succM M count)next).
 { apply(proj2(source_def_iteration_succ M true count(code_numeral M(sf_encode source_def_empty))next)). exists environment;auto. }
 destruct(source_canonical_parameter_assignment_total M count value)as(pb&pc&vb&vc&HOffset&HV).
 destruct(environment_cons_total M pb pc count old)as(ob&oc&on&HO).
 pose proof(proj1 HO)as EON. subst on.
 destruct(environment_cons_total M vb vc(succM M count)new)as(nb&nc&nn&HN).
 pose proof(proj1 HN)as ENN. subst nn.
 destruct(numerical_substitution_total M environment ob oc(succM M count)(zeroM M))as(previous&HP).
 destruct(numerical_substitution_total M next nb nc(succM M(succM M count))(zeroM M))as(target0&HT).
 pose proof(source_local_assigned_environment_bound M count environment pb pc old ob oc previous k HE HOffset HO HP BN5 CN8)as BPrevious.
 destruct(source_local_canonical_profile_open_total M phi count Ltarget selected value BF HLtarget CN0
  (proj2(coding_lt_succ_cancel M selected value)(source_local_high_name_order M base 0 6 ltac:(lia))))
 as(Lbody&inL&allProfile&canonicalPoint&assignedPhi&relative&memberValue&inSelected&newPair&HLTarget&HInL&HLBody&HAll&HRename&HRelative&HMemberValue&HInSelected&HNewPair&HProfile&BLBody&BAll&BProfile&BRelative).
 pose proof(source_canonical_parameter_assignment M count pb pc value vb vc phi assignedPhi BF HOffset HV HRename)as HAssigned.
 destruct(code_relation_total M EIC_ext_expression(EIC_ext_roles old new value))as(extension&HExt).
 destruct(sf_relation_total M SFMember new d)as(memberResult&HMemberResult).
 destruct(source_iff_total M memberResult relative)as(result&HResult).
 destruct(code_relation_total M source_local_SC_expression(local_SC_names d old value))as(sc&HSC).
 destruct(source_iff_total M sc relative)as(final&HFinal).
 destruct(sf_relation_total M SFImpl memberValue final)as(guard&HGuard).
 destruct(code_relation_total M source_local_operation5_expression(local_operation5_names d old(zeroM M)selected))as(operation&HOp).
 destruct(sf_relation_total M SFAnd memberValue sc)as(rawPair&HRawPair).
 destruct(source_iff_total M inSelected rawPair)as(rawProfile&HRawProfile).
 destruct(sf_relation_total M SFMember selected closure)as(selectedInClosure&HSelectedClosure).
 destruct(code_relation_total M source_local_subset_expression(local_subset_names selected(zeroM M)))as(subset&HSubset).
 destruct(sf_relation_total M SFMember selected definables)as(selectedInDef&HSelectedDef).
 destruct(sf_relation_total M SFImpl subset selectedInDef)as(accessTail&HAccessTail).
 destruct(sf_relation_total M SFImpl selectedInClosure accessTail)as(accessPoint&HAccessPoint).
 destruct(code_relation_total M source_local_access_expression(local_access_names closure(zeroM M)definables))as(accessAll&HAccessAll).
 destruct(sf_relation_total M SFImpl inSelected memberValue)as(subsetPoint&HSubsetPoint).
 destruct(sf_relation_total M SFAnd selectedInDef allProfile)as(profileBody&HProfileBody).
 destruct(source_named_quantifier_total M false selected profileBody)as(target&HTarget).
 destruct(code_relation_total M source_local_successor_expression(local_subset_names(zeroM M)successor))as(succ&HSucc).
 destruct(code_relation_total M source_local_closure_expression(local_subset_names successor closure))as(closureCode&HClosure).
 destruct(source_local_condition_three_roles M(zeroM M)successor closure succ closureCode HSucc HClosure)as(HSucc3&HClosure3).
 destruct(sf_relation_total M SFMember d closure)as(repInClosure&HRepInClosure).
 destruct(sf_relation_total M SFMember old closure)as(oldInClosure&HOldInClosure).
 destruct(sf_relation_total M SFAnd selectedInClosure operation)as(sourceBody&HSourceBody).
 destruct(code_relation_total M source_local_selection_exists_expression(local_selection_exists_roles(zeroM M)successor closure d old))as(sourceEx&HSourceEx).
 destruct(sf_relation_total M SFAnd previous oldInClosure)as(envBody&HEnvBody).
 destruct(source_named_quantifier_total M false old envBody)as(envEx&HEnvEx).
 destruct(sf_relation_total M SFAnd repInClosure assignedRep)as(repBody&HRepBody).
 destruct(source_named_quantifier_total M false d repBody)as(repEx&HRepEx).
 destruct(code_relation_total M source_local_def_predicate_expression(local_def_names(zeroM M)definables))as(predicate&HDef).
 destruct(sf_relation_total M SFAnd succ closureCode)as(contentPair&HContentPair).
 destruct(sf_relation_total M SFAnd contentPair accessAll)as(content&HContent).
 pose proof(source_local_unpack_content_graph M(zeroM M)definables successor closure succ closureCode accessAll contentPair content HSucc HClosure HAccessAll HContentPair HContent)as HContentGraph.

 assert(BZeroK:coding_lt M(zeroM M)k)by(exact(source_bound_lt_le M _ _ _(coding_zero_lt_succ M count)CN8)).
 assert(HMembers:source_dn_parameter_proofs M count pb pc(zeroM M)gb gc gn).
 { intros i v member HI HBeta HMember. pose proof(proj1(HOffset i v HI)HBeta)as E.
   change(v=addM M i(succM M(zeroM M)))in E. rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero in E.
   subst v. exact(HParameters i member HI HMember). }
 assert(HFresh:forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old).
 { intros i v HI HBeta. pose proof(proj1(HOffset i v HI)HBeta)as E.
   change(v=addM M i(succM M(zeroM M)))in E. rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero in E. subst v.
   exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _
    (source_bound_lt_le M _ _ _(proj2(coding_lt_succ_cancel M i count)HI)CN5)). }
 assert(BExt:source_bounded M extension k).
 { apply(source_parameter_graph_bounded M 3 source_def_extension021 source_def_extension_bound source_three_parameter_names(EIC_ext_roles old new value)k);[|exact HExt].
   intros[|[|[|i]]]v HI HX;try lia;cbn[source_three_parameter_names EIC_ext_roles code_relation]in HX;subst v;assumption. }
 assert(BSC:source_bounded M sc k).
 { apply(source_local_finite_parameter_bound M 3 source_local_SC source_local_SC_bound(local_SC_names d old value)k sc);[|exact HSC].
   intros[|[|[|i]]]HI;try lia;cbn[local_SC_names];assumption. }
 assert(BOp:source_bounded M operation k).
 { apply(source_local_finite_parameter_bound M 4 source_local_operation5 source_local_operation5_bound(local_operation5_names d old(zeroM M)selected)k operation);[|exact HOp].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_operation5_names];assumption. }
 assert(BSubset:source_bounded M subset k).
 { apply(source_local_finite_parameter_bound M 2 source_local_subset source_local_subset_bound(local_subset_names selected(zeroM M))k subset);[|exact HSubset].
   intros[|[|i]]HI;try lia;cbn[local_subset_names];assumption. }
 assert(BContent:source_bounded M content k).
 { apply(source_local_finite_parameter_bound M 4 source_local_unpack_content source_local_unpack_content_bound(local_unpack_content_names closure successor(zeroM M)definables)k content);[|exact HContentGraph].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_unpack_content_names];assumption. }
 assert(BPredicate:source_bounded M predicate k).
 { apply(source_local_finite_parameter_bound M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)k predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(B_memberResult:source_bounded M memberResult k).
 { apply(proj2(source_bounded_accept_atom M SFMember new d memberResult k(or_introl eq_refl)HMemberResult)). split;assumption. }
 assert(B_memberValue:source_bounded M memberValue k).
 { apply(proj2(source_bounded_accept_atom M SFMember value (zeroM M) memberValue k(or_introl eq_refl)HMemberValue)). split;assumption. }
 assert(B_inSelected:source_bounded M inSelected k).
 { apply(proj2(source_bounded_accept_atom M SFMember value selected inSelected k(or_introl eq_refl)HInSelected)). split;assumption. }
 assert(B_selectedInClosure:source_bounded M selectedInClosure k).
 { apply(proj2(source_bounded_accept_atom M SFMember selected closure selectedInClosure k(or_introl eq_refl)HSelectedClosure)). split;assumption. }
 assert(B_selectedInDef:source_bounded M selectedInDef k).
 { apply(proj2(source_bounded_accept_atom M SFMember selected definables selectedInDef k(or_introl eq_refl)HSelectedDef)). split;assumption. }
 assert(B_repInClosure:source_bounded M repInClosure k).
 { apply(proj2(source_bounded_accept_atom M SFMember d closure repInClosure k(or_introl eq_refl)HRepInClosure)). split;assumption. }
 assert(B_oldInClosure:source_bounded M oldInClosure k).
 { apply(proj2(source_bounded_accept_atom M SFMember old closure oldInClosure k(or_introl eq_refl)HOldInClosure)). split;assumption. }
 assert(B_relative:source_bounded M relative k)by(exact(source_bounded_monotone M relative (succM M value) k BRelative(proj2(coding_lt_succ_cancel M _ _)BN6))).
 assert(B_allProfile:source_bounded M allProfile k)by(exact(source_bounded_monotone M allProfile (succM M selected) k BAll(proj2(coding_lt_succ_cancel M _ _)BN0))).
 assert(B_Lbody:source_bounded M Lbody k)by(exact(source_bounded_monotone M Lbody (succM M selected) k BLBody(proj2(coding_lt_succ_cancel M _ _)BN0))).
 assert(B_accessTail:source_bounded M accessTail k).
 { apply(proj2(source_bounded_accept_binary M SFImpl subset selectedInDef accessTail k(or_intror(or_intror eq_refl))HAccessTail)). split;assumption. }
 assert(B_accessPoint:source_bounded M accessPoint k).
 { apply(proj2(source_bounded_accept_binary M SFImpl selectedInClosure accessTail accessPoint k(or_intror(or_intror eq_refl))HAccessPoint)). split;assumption. }
 assert(B_profileBody:source_bounded M profileBody k).
 { apply(proj2(source_bounded_accept_binary M SFAnd selectedInDef allProfile profileBody k(or_introl eq_refl)HProfileBody)). split;assumption. }
 assert(B_sourceBody:source_bounded M sourceBody k).
 { apply(proj2(source_bounded_accept_binary M SFAnd selectedInClosure operation sourceBody k(or_introl eq_refl)HSourceBody)). split;assumption. }
 assert(B_envBody:source_bounded M envBody k).
 { apply(proj2(source_bounded_accept_binary M SFAnd previous oldInClosure envBody k(or_introl eq_refl)HEnvBody)). split;assumption. }
 assert(B_repBody:source_bounded M repBody k).
 { apply(proj2(source_bounded_accept_binary M SFAnd repInClosure assignedRep repBody k(or_introl eq_refl)HRepBody)). split;assumption. }

 assert(BDefMemberSmall:source_bounded M selectedInDef(succM M definables)).
 { apply(proj2(source_bounded_accept_atom M SFMember selected definables selectedInDef(succM M definables)(or_introl eq_refl)HSelectedDef)).
   split;[exact(coding_lt_trans M _ _ _(source_local_high_name_order M base 0 1 ltac:(lia))(coding_lt_succ M definables))|apply coding_lt_succ]. }
 assert(BAllSmall:source_bounded M allProfile(succM M definables)).
 { exact(source_bounded_monotone M allProfile(succM M selected)(succM M definables)BAll
   (proj2(coding_lt_succ_cancel M selected(succM M definables))(coding_lt_trans M _ _ _(source_local_high_name_order M base 0 1 ltac:(lia))(coding_lt_succ M definables)))). }
 assert(BProfileSmall:source_bounded M profileBody(succM M definables)).
 { apply(proj2(source_bounded_accept_binary M SFAnd selectedInDef allProfile profileBody(succM M definables)(or_introl eq_refl)HProfileBody)). auto. }
 pose proof(source_named_quantifier_bound M false selected profileBody target(succM M definables)BProfileSmall HTarget)as BTargetSmall.
 assert(NZ0:selected<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound selected BContext GN0)as VC_selected.
 assert(NZ1:definables<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound definables BContext GN1)as VC_definables.
 assert(NZ2:successor<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound successor BContext GN2)as VC_successor.
 assert(NZ3:closure<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound closure BContext GN3)as VC_closure.
 assert(NZ4:d<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound d BContext GN4)as VC_d.
 assert(NZ5:old<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound old BContext GN5)as VC_old.
 assert(NZ6:value<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound value BContext GN6)as VC_value.
 assert(NZ7:new<>zeroM M)by(congruence).
 pose proof(source_named_context_vacuous_above_bound M gb gc gn contextBound new BContext GN7)as VC_new.
 assert(VTarget_successor:source_named_vacuous M successor target).
 { exact(source_named_vacuous_above_bound M target successor(succM M definables)BTargetSmall(proj2(coding_lt_succ_cancel M definables successor)(source_local_high_name_order M base 1 2 ltac:(lia)))). }
 assert(VTarget_closure:source_named_vacuous M closure target).
 { exact(source_named_vacuous_above_bound M target closure(succM M definables)BTargetSmall(proj2(coding_lt_succ_cancel M definables closure)(source_local_high_name_order M base 1 3 ltac:(lia)))). }
 assert(VTarget_d:source_named_vacuous M d target).
 { exact(source_named_vacuous_above_bound M target d(succM M definables)BTargetSmall(proj2(coding_lt_succ_cancel M definables d)(source_local_high_name_order M base 1 4 ltac:(lia)))). }
 assert(VTarget_old:source_named_vacuous M old target).
 { exact(source_named_vacuous_above_bound M target old(succM M definables)BTargetSmall(proj2(coding_lt_succ_cancel M definables old)(source_local_high_name_order M base 1 5 ltac:(lia)))). }

 pose proof(source_named_vacuous_above_bound M relative new(succM M value)BRelative
  (proj2(coding_lt_succ_cancel M value new)(source_local_high_name_order M base 6 7 ltac:(lia))))as VRelative.
 pose proof(source_named_vacuous_above_bound M Ltarget definables(succM M count)
  (source_L_definable_profile_bounded M count phi Ltarget BF HLtarget)CN1)as VLTarget.
 assert(V_operation_new:source_named_vacuous M new operation).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_operation5 source_local_operation5_bound(local_operation5_names d old(zeroM M)selected)new operation);[|exact HOp].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_operation5_names];assumption. }
 assert(V_operation_value:source_named_vacuous M value operation).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_operation5 source_local_operation5_bound(local_operation5_names d old(zeroM M)selected)value operation);[|exact HOp].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_operation5_names];assumption. }
 assert(V_content_new:source_named_vacuous M new content).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_unpack_content source_local_unpack_content_bound(local_unpack_content_names closure successor(zeroM M)definables)new content);[|exact HContentGraph].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_unpack_content_names];assumption. }
 assert(V_content_value:source_named_vacuous M value content).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_unpack_content source_local_unpack_content_bound(local_unpack_content_names closure successor(zeroM M)definables)value content);[|exact HContentGraph].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_unpack_content_names];assumption. }
 assert(V_content_selected:source_named_vacuous M selected content).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_unpack_content source_local_unpack_content_bound(local_unpack_content_names closure successor(zeroM M)definables)selected content);[|exact HContentGraph].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_unpack_content_names];assumption. }
 assert(V_content_old:source_named_vacuous M old content).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_unpack_content source_local_unpack_content_bound(local_unpack_content_names closure successor(zeroM M)definables)old content);[|exact HContentGraph].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_unpack_content_names];assumption. }
 assert(V_content_d:source_named_vacuous M d content).
 { apply(source_local_finite_parameter_vacuous M 4 source_local_unpack_content source_local_unpack_content_bound(local_unpack_content_names closure successor(zeroM M)definables)d content);[|exact HContentGraph].
   intros[|[|[|[|i]]]]HI;try lia;cbn[local_unpack_content_names];assumption. }
 assert(V_predicate_new:source_named_vacuous M new predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)new predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(V_predicate_value:source_named_vacuous M value predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)value predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(V_predicate_selected:source_named_vacuous M selected predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)selected predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(V_predicate_old:source_named_vacuous M old predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)old predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(V_predicate_d:source_named_vacuous M d predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)d predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(V_predicate_closure:source_named_vacuous M closure predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)closure predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 assert(V_predicate_successor:source_named_vacuous M successor predicate).
 { apply(source_local_finite_parameter_vacuous M 2 source_local_def_predicate source_local_def_predicate_bound(local_def_names(zeroM M)definables)successor predicate);[|exact HDef].
   intros[|[|i]]HI;try lia;cbn[local_def_names];assumption. }
 pose proof(source_local_assigned_environment_vacuous M count environment pb pc old ob oc previous k new HE HOffset HO HP BPrevious N57 CN7)as VPrevious_new.
 pose proof(source_local_assigned_environment_vacuous M count environment pb pc old ob oc previous k value HE HOffset HO HP BPrevious N56 CN6)as VPrevious_value.
 pose proof(source_local_assigned_environment_vacuous M count environment pb pc old ob oc previous k selected HE HOffset HO HP BPrevious N50 CN0)as VPrevious_selected.
 pose proof(source_local_assigned_representation_vacuous M rep(zeroM M)d rb rc assignedRep new BRep HOpen HAssignedRep ZN7 N47)as VAssignedRep_new.
 pose proof(source_local_assigned_representation_vacuous M rep(zeroM M)d rb rc assignedRep value BRep HOpen HAssignedRep ZN6 N46)as VAssignedRep_value.
 pose proof(source_local_assigned_representation_vacuous M rep(zeroM M)d rb rc assignedRep selected BRep HOpen HAssignedRep ZN0 N40)as VAssignedRep_selected.
 pose proof(source_local_assigned_representation_vacuous M rep(zeroM M)d rb rc assignedRep old BRep HOpen HAssignedRep ZN5 N45)as VAssignedRep_old.
 pose proof(source_named_vacuous_binary M SFAnd selectedInClosure operation sourceBody new(or_introl eq_refl)HSourceBody (source_named_member_vacuous M selected closure selectedInClosure new N07 N37 HSelectedClosure) V_operation_new)as V_sourceBody_new.
 pose proof(source_named_vacuous_binary M SFAnd selectedInClosure operation sourceBody value(or_introl eq_refl)HSourceBody (source_named_member_vacuous M selected closure selectedInClosure value N06 N36 HSelectedClosure) V_operation_value)as V_sourceBody_value.
 pose proof(source_named_vacuous_binary M SFAnd previous oldInClosure envBody new(or_introl eq_refl)HEnvBody VPrevious_new (source_named_member_vacuous M old closure oldInClosure new N57 N37 HOldInClosure))as V_envBody_new.
 pose proof(source_named_vacuous_binary M SFAnd previous oldInClosure envBody value(or_introl eq_refl)HEnvBody VPrevious_value (source_named_member_vacuous M old closure oldInClosure value N56 N36 HOldInClosure))as V_envBody_value.
 pose proof(source_named_vacuous_binary M SFAnd previous oldInClosure envBody selected(or_introl eq_refl)HEnvBody VPrevious_selected (source_named_member_vacuous M old closure oldInClosure selected N50 N30 HOldInClosure))as V_envBody_selected.
 pose proof(source_named_vacuous_binary M SFAnd repInClosure assignedRep repBody new(or_introl eq_refl)HRepBody (source_named_member_vacuous M d closure repInClosure new N47 N37 HRepInClosure) VAssignedRep_new)as V_repBody_new.
 pose proof(source_named_vacuous_binary M SFAnd repInClosure assignedRep repBody value(or_introl eq_refl)HRepBody (source_named_member_vacuous M d closure repInClosure value N46 N36 HRepInClosure) VAssignedRep_value)as V_repBody_value.
 pose proof(source_named_vacuous_binary M SFAnd repInClosure assignedRep repBody selected(or_introl eq_refl)HRepBody (source_named_member_vacuous M d closure repInClosure selected N40 N30 HRepInClosure) VAssignedRep_selected)as V_repBody_selected.
 pose proof(source_named_vacuous_binary M SFAnd repInClosure assignedRep repBody old(or_introl eq_refl)HRepBody (source_named_member_vacuous M d closure repInClosure old N45 N35 HRepInClosure) VAssignedRep_old)as V_repBody_old.

 apply(source_full_local_L_definability_exists_from_data M count phi rep d(zeroM M)rb rc assignedRep pb pc value vb vc
 environment next old ob oc previous new nb nc target0 extension memberValue memberResult relative assignedPhi result
 fb fc fn gb gc gn k sc final guard selected operation inSelected rawPair rawProfile newPair canonicalPoint allProfile
 closure definables selectedInClosure subset selectedInDef accessTail accessPoint accessAll subsetPoint profileBody target
 successor succ closureCode repInClosure oldInClosure sourceBody sourceEx envClosure envBody envEx repClosure repBody repEx predicate contentPair content
 ordinalName ordinal level inL Lbody Ltarget);try assumption.
 - intros[|[|[|[|[|[|i]]]]]]HI;try lia;cbn[local_selection_exists_roles];assumption.
Qed.
Print Assumptions source_full_local_L_definability_canonical.
