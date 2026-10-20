(** Actual closure-extension law in the canonical A0/S1/C2/head3
    frame. The chosen old/output witnesses remain arbitrary model values. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift SourceDefinabilityPrimitives
 SourceEnvInClosureFixed SourceEnvInClosureConstructor SourceEnvInClosureExtensionBinder SourceEnvInClosureWitnessShell
 SourceNamedQuantifierRules SchemaConstructorBounds SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterIdentityCalibration SourcePropositionalRebase
 SourceNumFClosureRecipe SourceRepresentationClosureRecipe SourcePropositionalTemplates SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition EIC_fixed_roles M e i:=match i with 0=>zeroM M|1=>code_numeral M 1|2=>code_numeral M 2|3=>e|_=>code_numeral M 3 end.
Definition EIC_fixed_values M oldmem headmem ex i:=match i with
 0=>numf_closure_succ_code M|1=>numf_closure_condition_code M|2=>oldmem|3=>headmem|9=>ex|_=>zeroM M end.
Local Opaque source_def_successor01 representation_closure_condition.
Theorem source_zfr_env_in_closure_extension_instance M e z oldmem headmem member extension body:
 sf_relation M SFMember e(code_numeral M 2)oldmem->
 sf_relation M SFMember(code_numeral M 3)(zeroM M)headmem->
 sf_relation M SFMember z(code_numeral M 2)member->
 code_relation M(EIC_ext_roles e z(code_numeral M 3))EIC_ext_expression extension->
 sf_relation M SFAnd member extension body->
 z<>zeroM M->z<>code_numeral M 1->z<>code_numeral M 2->z<>e->z<>code_numeral M 3->
 exists ex law,source_named_quantifier M false z body ex /\
 code_relation M(EIC_fixed_values M oldmem headmem ex)(source_prop_expression EIW_fixed)law /\source_zfr_provable M law.
Proof.
 intros HOld HHead HMember HExt HBody HZ0 HZ1 HZ2 HZE HZ3.
 set(rho:=EIC_fixed_roles M e).
 destruct(code_relation_total M source_env_in_closure_extension_expression rho)as(law&HLaw).
 pose proof(source_zfr_env_in_closure_extension M rho law HLaw)as PLaw.
 rewrite eic_extension_law_shape in HLaw.
 destruct(schema_expression_split M rho SFImpl _ _ law HLaw)as(s&mid&HS&HMid&HLawOut).
 assert(HSC:code_relation M rho(source_parameter_expression(source_finite_parameter_names 5)source_def_successor01)(numf_closure_succ_code M)).
 { apply(proj2(source_parameter_graph_ext M 2 source_def_successor01 source_def_successor_bound
    (source_finite_parameter_names 5)CEconst rho(fun _=>zeroM M)
    ltac:(intros[|[|i]]v HI;try lia;reflexivity)(numf_closure_succ_code M))).
   exact(source_parameter_identity_calibration M source_def_successor01 CEconst(fun _=>zeroM M)(fun i=>eq_refl)). }
 rewrite(code_relation_functional M _ rho s _ HS HSC)in HLawOut.
 destruct(schema_expression_split M rho SFImpl _ _ mid HMid)as(c&tail&HC&HTail&HMidOut).
 assert(HCC:code_relation M rho(source_parameter_expression(source_finite_parameter_names 5)representation_closure_condition)(numf_closure_condition_code M)).
 { apply(proj2(source_parameter_graph_ext M 3 representation_closure_condition representation_closure_finite_bound
    (source_finite_parameter_names 5)CEconst rho(fun _=>zeroM M)
    ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)(numf_closure_condition_code M))).
   exact(source_parameter_identity_calibration M representation_closure_condition CEconst(fun _=>zeroM M)(fun i=>eq_refl)). }
 rewrite(code_relation_functional M _ rho c _ HC HCC)in HMidOut.
 destruct(schema_expression_split M rho SFImpl _ _ tail HTail)as(old&last&HOldGraph&HLast&HTailOut).
 assert(HOldGraph':code_relation M rho(E_sf SFMember(CEvar 3)(CEvar 2))oldmem).
 { apply(proj2(schema_expression_graph M rho SFMember(CEvar 3)(CEvar 2)e(code_numeral M 2)oldmem eq_refl eq_refl)). exact HOld. }
 rewrite(code_relation_functional M _ rho old oldmem HOldGraph HOldGraph')in HTailOut.
 destruct(schema_expression_split M rho SFImpl _ _ last HLast)as(head&ex&HHeadGraph&HEx&HLastOut).
 assert(HHeadGraph':code_relation M rho(E_sf SFMember(CEvar 4)(CEvar 0))headmem).
 { apply(proj2(schema_expression_graph M rho SFMember(CEvar 4)(CEvar 0)(code_numeral M 3)(zeroM M)headmem eq_refl eq_refl)). exact HHead. }
 rewrite(code_relation_functional M _ rho head headmem HHeadGraph HHeadGraph')in HLastOut.
 exists ex,law. split.
 - apply(source_env_in_closure_extension_named M rho z member extension body ex);try assumption.
   intros[|[|[|[|[|i]]]]]HI;try lia;cbn[rho EIC_fixed_roles];assumption.
 - split;[|exact PLaw]. unfold EIW_fixed.
   eapply source_prop_template_join;[reflexivity| |exact HLawOut].
   eapply source_prop_template_join;[reflexivity| |exact HMidOut].
   eapply source_prop_template_join;[reflexivity| |exact HTailOut].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HLastOut].
Qed.
Print Assumptions source_zfr_env_in_closure_extension_instance.
