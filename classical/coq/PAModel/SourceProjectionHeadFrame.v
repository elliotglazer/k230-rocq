(** A syntactic/hygienic projection frame and its actual ZFR proof.
    This record contains only code graphs, bounds and vacuity; no source
    provability field or representation-correctness premise is hidden in it. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SchemaConstructorBounds SourceBounded SourcePropositionalTemplates
 SourceRepresentationDifferenceProgram SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceNamedVacuity SourceNamedQuantifierRules
 SourceProjectionHeadPoint SourceProjectionGuardedTransfer SourceProjectionHeadAssembly SourceProjectionFiniteBinders
 SourceProjectionProfilePoint SourceProjectionExtensionBinder SourceProjectionOperationFixed SourceProjectionFiniteSyntax
 SourceEnvironmentExtensionScopes SourceDefinabilityPrimitives SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterProofs
 SourceZFRProvability SourceSetTheoryDescriptors SourceIffGraphs.
Unset Implicit Arguments.
Record source_projection_head_frame M an child p a e(values:nat->carrier M)(k:carrier M):Prop:={
 PHF_bounds:forall i,source_bounded M(values i)k;
 PHF_e_a:e<>a;PHF_e_child:e<>child;PHF_e_p:e<>p;
 PHF_a_child:a<>child;PHF_a_carrier:a<>code_numeral M 1;PHF_a_p:a<>p;
 PHF_extension:code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)(values 1);
 PHF_child_member:sf_relation M SFMember e child(values 2);
 PHF_carrier_member:sf_relation M SFMember a(code_numeral M 1)(values 4);
 PHF_An_member:sf_relation M SFMember p an(values 13);
 PHF_result_member:sf_relation M SFMember p(zeroM M)(values 14);
 PHF_operation:code_relation M(projection_five_values an child(code_numeral M 1)(zeroM M)p)
  (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)(values 15);
 PHF_inner:code_relation M(projection_three_values a child p)
  (source_parameter_expression(source_finite_parameter_names 3)projection_inner3)(values 9);
 PHF_profile:code_relation M(projection_three_values child(code_numeral M 1)p)
  (source_parameter_expression(source_finite_parameter_names 3)projection_PJ3)(values 11);
 PHF_ext_exists:code_relation M(projection_two_values p a)source_projection_extension_expression(values 8);
 PHF_syntax:exists previouspair headbody localbody extbody projectionpair guardedbody left right coveragebody parentbody,
  code_relation M values(source_prop_expression(SPTAnd(SPTSlot 0)(SPTSlot 1)))previouspair /\
  source_named_quantifier M false p previouspair(values 5) /\
  code_relation M values(source_prop_expression EPH_head_body)headbody /\source_named_quantifier M true a headbody(values 7) /\
  code_relation M values(source_prop_expression EPH_local_body)localbody /\source_named_quantifier M true e localbody(values 6) /\
  code_relation M values(source_prop_expression EPH_ext_body)extbody /\source_named_quantifier M true e extbody(values 10) /\
  code_relation M values(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 1)))projectionpair /\
  code_relation M values(source_prop_expression EPG_body)guardedbody /\source_named_quantifier M true a guardedbody(values 18) /\
  code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 9)))left /\
  code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 3)))right /\source_named_quantifier M false a right(values 12) /\
  code_relation M values(source_prop_expression EPA_coverage_body)coveragebody /\source_named_quantifier M true p coveragebody(values 16) /\
  code_relation M values(source_prop_expression EPA_parent_body)parentbody /\source_named_quantifier M true p parentbody(values 17);
 PHF_vacuity:source_named_vacuous M e(values 7) /\source_named_vacuous M e(values 4) /\
  source_named_vacuous M e(values 0) /\source_named_vacuous M e(values 3) /\
  source_named_vacuous M a(values 7) /\source_named_vacuous M a(values 0) /\
  source_named_vacuous M p(values 15) /\source_named_vacuous M p(values 7) /\source_named_vacuous M p(values 16)
}.
Theorem source_zfr_projection_head_frame M an child p a e values k result:
 source_projection_head_frame M an child p a e values k ->
 code_relation M values(source_prop_expression EPA_result)result ->source_zfr_provable M result.
Proof.
 intros HFrame HResult.
 destruct HFrame as[HB EA EC EP AC AA AP HExt HMem HCarrier HAn HResultMem HOp HInner HProfile HExExt HS HV].
 destruct HS as(previouspair&headbody&localbody&extbody&projectionpair&guardedbody&left&right&coveragebody&parentbody&
  HPrevious&HExP&HHead&HAllA&HLocal&HAllE&HExtBody&HAllExt&HPair&HGuarded&HAllGuarded&HL&HR&HExR&HC&HCov&HP&HParent).
 destruct HV as(VHe&VAe&VPe&VTe&VHa&VPa&VOp&VHp&VCp).
 assert(HExInner:source_named_quantifier M false e projectionpair(values 9)).
 { exact(source_projection_inner_named_exists M a child p e(values 1)(values 2)projectionpair(values 9)
   EA EC EP HExt HMem(proj1(schema_expression_graph M values SFAnd(CEvar 2)(CEvar 1)(values 2)(values 1)projectionpair eq_refl eq_refl)HPair)HInner). }
 assert(HExProfile:source_named_quantifier M false a left(values 11)).
 { exact(source_projection_outer_named_exists M child(code_numeral M 1)p a(values 9)(values 4)left(values 11)
   AC AA AP HInner HCarrier(proj1(schema_expression_graph M values SFAnd(CEvar 4)(CEvar 9)(values 4)(values 9)left eq_refl eq_refl)HL)HProfile). }
 assert(HExists:source_named_quantifier M false e(values 1)(values 8)).
 { exact(source_projection_extension_named_exists M p a e(values 1)(values 8)EP EA HExt HExExt). }
 assert(PExt:source_descriptor_provable M ZFRSourceDescriptor(values 8)).
 { exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_projection_extension M(projection_two_values p a)(values 8)HExExt)). }
 assert(PPoint:source_descriptor_template M ZFRSourceDescriptor values EPH_result).
 { intros f HF. exact(source_descriptor_projection_head_point M ZFRSourceDescriptor values a e p previouspair headbody localbody extbody projectionpair f k
   HB HPrevious HExP HHead HAllA HLocal HAllE HExtBody HAllExt HExists HPair HExInner VHe VAe VPe VTe PExt HF). }
 assert(PGuarded:source_descriptor_template M ZFRSourceDescriptor values EPG_result).
 { intros f HF. exact(source_descriptor_projection_guarded_transfer M ZFRSourceDescriptor values a guardedbody left right f k
   HB HGuarded HAllGuarded HL HExProfile HR HExR VHa VPa PPoint HF). }
 assert(POp:source_descriptor_template M ZFRSourceDescriptor values EPA_operation).
 { intros f HF.
   destruct(source_prop_template_binary M values SFImpl(SPTSlot 15)(SPTImpl(SPTSlot 13)(SPTIff(SPTSlot 14)(SPTSlot 11)))f HF)
    as(op&inner&GOp&GInner&HOuter). change(op=values 15)in GOp. subst op.
   destruct(source_prop_template_binary M values SFImpl(SPTSlot 13)(SPTIff(SPTSlot 14)(SPTSlot 11))inner GInner)
    as(inAn&equiv&GAn&GEquiv&HInside). change(inAn=values 13)in GAn. subst inAn.
   apply(proj2(source_zfr_descriptor_provable M f)).
   refine(source_zfr_projection_profile_point M an child(code_numeral M 1)(zeroM M)p(values 15)(values 13)(values 14)(values 11)equiv inner f
    HOp HAn HResultMem HProfile _ HInside HOuter).
   exact GEquiv. }
 apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_projection_head_assembly M ZFRSourceDescriptor values p coveragebody parentbody result k
  HB HC HCov HP HParent VOp VHp VCp PGuarded POp HResult).
Qed.
Print Assumptions source_zfr_projection_head_frame.
