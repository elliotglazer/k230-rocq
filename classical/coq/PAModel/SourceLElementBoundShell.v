(** The actual strong L bound in its canonical raw-set slot0 shell. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes SetSchemaConstructors NumericalInstantiation
 SourceLFixed SourceLElementBoundOld SourceLElementBoundFixed SourceLReplacementCutShells
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterComposition SourceHierarchyWitnessShell SourceOrdinalMemberShell SourceDomainInstances SourceLNonempty
 SourcePropositionalRebase SourceFunctionalityShells SourceWFSeparationConstructor SourceZFRProvability OldNamedSyntaxBridge SubstitutionSource.
From OldZFC Require Z_L.
Unset Implicit Arguments.
Local Opaque source_L_domain source_L_domain_code.
Theorem source_zfr_L_element_bound_shell M:exists bound,
 code_relation M(schema_env3(source_L_domain_code M)(zeroM M)(zeroM M))
  (E_L_cover_witness(CEvar 0))bound /\source_zfr_provable M bound.
Proof.
 set(rho:=fun _:nat=>zeroM M). set(names:=source_finite_parameter_names 1).
 set(up1:=source_parameter_up names). set(up2:=source_parameter_up up1).
 destruct(code_relation_total M source_L_element_bound_expression rho)as(bound&HG).
 pose proof(source_zfr_L_element_bound M rho bound HG)as PBound.
 unfold source_L_element_bound_expression,source_L_element_bound_law,old_L_element_bound_law in HG.
 change(code_relation M rho(E_sf SFEx(E_sf SFAnd
  (source_parameter_expression up1(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 0))))
  (E_sf SFAll(E_sf SFImpl(E_sf SFMember(up2 0)(up2 2))
   (E_sf SFImpl(source_parameter_expression up2(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 0))))
    (E_sf SFMember(up2 0)(up2 1))))(CEconst 0)))(CEconst 0))bound)in HG.
 destruct(schema_expression_quantifier_split M _ SFEx _ bound HG)as(body&HBody&HEx).
 destruct(schema_expression_split M _ SFAnd _ _ body HBody)as(inL&all&HInL&HAll&HAnd).
 destruct(schema_expression_quantifier_split M _ SFAll _ all HAll)as(point&HPoint&HAllQ).
 destruct(schema_expression_split M _ SFImpl _ _ point HPoint)as(member&tail&HMember&HTail&HImp).
 destruct(schema_expression_split M _ SFImpl _ _ tail HTail)as(inL'&memberY&HInL'&HMemberY&HTailImp).
 assert(U0:code_relation M rho(up1 0)(zeroM M))by reflexivity.
 assert(V0:code_relation M rho(up2 0)(zeroM M))by reflexivity.
 assert(V1:code_relation M rho(up2 1)(code_numeral M 1)).
 { exact(source_code_successor_graph M rho(CEconst 0)(zeroM M)eq_refl). }
 assert(V2:code_relation M rho(up2 2)(code_numeral M 2)).
 { apply(source_code_successor_graph M rho(up1 1)(code_numeral M 1)).
   exact(source_code_successor_graph M rho(names 0)(zeroM M)eq_refl). }
 pose proof(source_parameter_L_instance M up1 rho 0(zeroM M)inL U0 HInL)as HI.
 pose proof(source_parameter_L_instance M up2 rho 0(zeroM M)inL' V0 HInL')as HI'.
 assert(E:inL=source_L_domain_code M)by(exact(numerical_instantiation_functional M _ _ inL _ HI
  (source_domain_instance_zero M(source_L_domain_code M)(numerical_L_domain_bounded M)))). subst inL.
 assert(E:inL'=source_L_domain_code M)by(exact(numerical_instantiation_functional M _ _ inL' _ HI'
  (source_domain_instance_zero M(source_L_domain_code M)(numerical_L_domain_bounded M)))). subst inL'.
 pose proof(proj1(substitution_source_constructor_graph M rho SFMember(up2 0)(up2 2)(zeroM M)(code_numeral M 2)member V0 V2)HMember)as HM.
 pose proof(proj1(substitution_source_constructor_graph M rho SFMember(up2 0)(up2 1)(zeroM M)(code_numeral M 1)memberY V0 V1)HMemberY)as HMY.
 exists bound. split;[|exact PBound]. unfold E_L_cover_witness,E_L_cover_profile,E_sf_all,E_sf_ex,E_sf_mem.
 functionality_graph.
Qed.
Print Assumptions source_zfr_L_element_bound_shell.




