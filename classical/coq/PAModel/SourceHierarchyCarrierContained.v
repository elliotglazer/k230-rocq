(** Actual guarded universal containment of any ordinal hierarchy carrier in L. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SchemaConstructorBounds
 SourceHierarchyContainmentOld SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift
 SourceFiniteParameters SourceFiniteNameParameters SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors
 SourceHierarchySyntax SourceHierarchyCalibration SourceHierarchyWitnessShell SourceOrdinalPredicate SourceOrdinalParameterCalibration
 SourceOrdinalMemberShell SourcePropositionalRebase SourceFiniteTelescope SubstitutionSource NumericalInstantiation SourceDomainInstances
 NumericalSourceFull SourceDerivedRules SourceTracePointRules SourceInstantiationConstructors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain source_L_domain_code source_ordinal_predicate source_LL_predicate.
Definition source_hierarchy_carrier_in_L M Lb out:=exists guard point,
 sf_relation M SFMember(zeroM M)(succM M Lb)guard /\
 sf_relation M SFImpl guard(source_L_domain_code M)point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_hierarchy_carrier_in_L_total M Lb:exists out,source_hierarchy_carrier_in_L M Lb out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M Lb))as(guard&HG).
 destruct(sf_relation_total M SFImpl guard(source_L_domain_code M))as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO).
 exists out,guard,point. auto.
Qed.
Definition source_hierarchy_carrier_expression:=source_parameter_expression(source_finite_parameter_names 2)
 (isolated_formula old_hierarchy_carrier_law).
Theorem source_zfr_hierarchy_carrier_named M rho out:
 code_relation M rho source_hierarchy_carrier_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(isolated_formula old_hierarchy_carrier_law)2 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_carrier_law
    old_L_background_valid old_hierarchy_carrier_proof).
 - exact HO.
Qed.
Theorem source_zfr_hierarchy_carrier_shell M beta Lb:
 exists ordinal level contained law,
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\source_LL_instance M beta Lb level /\
 source_hierarchy_carrier_in_L M Lb contained /\source_finite_telescope M[ordinal;level]contained law /\source_zfr_provable M law.
Proof.
 set(rho:=fun i:nat=>match i with 0=>beta|_=>Lb end). set(names:=source_finite_parameter_names 2).
 set(up:=source_parameter_up names).
 destruct(code_relation_total M source_hierarchy_carrier_expression rho)as(law&HLaw).
 pose proof(source_zfr_hierarchy_carrier_named M rho law HLaw)as PLaw.
 change(code_relation M rho(E_sf SFImpl
  (source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
  (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
   (E_sf SFAll(E_sf SFImpl(E_sf SFMember(up 0)(up 2))
    (source_parameter_expression up(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 0)))))(CEconst 0))))law)in HLaw.
 destruct(schema_expression_split M rho SFImpl _ _ law HLaw)as(ordinal&tail&HO&HT&HI0).
 destruct(schema_expression_split M rho SFImpl _ _ tail HT)as(level&contained&HL&HC&HI1).
 destruct(schema_expression_split M rho SFAll _ _ contained HC)as(point&z&HP&HZ&HAll).
 change(z=zeroM M)in HZ. subst z.
 destruct(schema_expression_split M rho SFImpl _ _ point HP)as(guard&inside&HG&HX&HImp).
 assert(U0:code_relation M rho(up 0)(zeroM M))by reflexivity.
 assert(U2:code_relation M rho(up 2)(succM M Lb)).
 { exact(source_code_successor_graph M rho(names 1)Lb eq_refl). }
 pose proof(source_parameter_L_instance M up rho 0(zeroM M)inside U0 HX)as HInside.
 assert(EInside:inside=source_L_domain_code M).
 { exact(numerical_instantiation_functional M(source_L_domain_code M)(zeroM M)inside(source_L_domain_code M)
   HInside(source_domain_instance_zero M(source_L_domain_code M)(numerical_L_domain_bounded M))). }
 subst inside.
 exists ordinal,level,contained,law.
 split;[exact(source_parameter_ordinal_instance M names rho 0 beta ordinal eq_refl HO)|].
 split;[exact(source_parameter_LL_instance M names rho 0 1 beta Lb level eq_refl eq_refl HL)|].
 split.
 - exists guard,point. split;[|auto]. exact(proj1(schema_expression_graph M rho SFMember(up 0)(up 2)(zeroM M)(succM M Lb)guard U0 U2)HG).
 - split;[|exact PLaw]. exists tail. split;[|exact HI0]. exists contained. split;[reflexivity|exact HI1].
Qed.
Theorem source_full_hierarchy_carrier_in_L_use M Lb x whole member inside gb gc gn:
 source_hierarchy_carrier_in_L M Lb whole ->sf_relation M SFMember x Lb member ->
 numerical_instantiation M(source_L_domain_code M)x inside ->
 source_full_prv M gb gc gn whole ->source_full_prv M gb gc gn member ->source_full_prv M gb gc gn inside.
Proof.
 intros(guard&point&HG&HP&HAll)HM HX PWhole PM.
 pose proof(source_instantiation_head_member M Lb guard x member HG HM)as HIG.
 destruct(sf_relation_total M SFImpl member inside)as(instance&HInstance).
 pose proof(source_instantiation_binary M SFImpl guard(source_L_domain_code M)point x member inside instance
  (or_intror(or_intror eq_refl))HP HIG HX HInstance)as HI.
 pose proof(full_source_AllE M gb gc gn point whole x instance
  (source_wf_quantifier_instance M gb gc gn SFAll point whole x instance(or_introl eq_refl)HAll
   (source_full_prv_wellformed M gb gc gn whole PWhole)HI)PWhole HAll HI)as PInstance.
 exact(source_full_modus_ponens M gb gc gn member inside instance HInstance PInstance PM).
Qed.
Print Assumptions source_hierarchy_carrier_in_L_total.
Print Assumptions source_zfr_hierarchy_carrier_named.
Print Assumptions source_zfr_hierarchy_carrier_shell.
Print Assumptions source_full_hierarchy_carrier_in_L_use.
