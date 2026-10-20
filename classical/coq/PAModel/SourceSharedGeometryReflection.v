(** Actual ordinary L-reflection from a valid superset geometry table.
    Every witness-closure proof is constructed from PH, internally collected,
    and used under the literal hierarchy binder. No image or proof-family
    premise occurs in the resulting source theorem. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes Pairing
 SourceBounded SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalContextRenaming
 NumericalInstantiation NumericalRenaming NumericalSourceFull ContextCombination SourceContextTransport
 SourceClosedContextShift SourceContextProofHelpers SourceProofWeakening SourceProofShiftCons SourceLeastOrdinalWitness
 SourceQuantifierRules SourceFiniteFamilyBounds SourceFiniteTelescope SourceZFRProvability SourceSetTheoryDescriptors SourceDescriptorProvability
 SourceQuantifierPieces SourcePieceWitnessInstance SourceOrdinalPredicate
 SourcePCSTables SourcePCSPieces SourcePieceConjunctionBounds SourceHierarchySyntax SourceLFixed
 SourceReflectionGeometryPoint SourceReflectionGeometryRenaming SourceReflectionGeometryElimination
 SourceGeometryPieceWitness SourceHierarchyCarrierContained SourceTarskiVaughtWitnessCollection
 SourceTarskiVaughtInputs SourceSetRelativizationRules SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionFromTV.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_zfr_geometry_ordinary_reflection_over_table M level gb gc gpieces sb sc pieces phi count seed K beta geometry refl law:
 source_bounded M level(code_numeral M 2) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
 source_bounded M phi count ->source_pcs_table M(source_L_domain_code M)phi count sb sc pieces ->
 source_piece_table_valid M gb gc gpieces ->context_included M sb sc pieces gb gc gpieces ->
 source_reflection_geometry_point M(source_L_domain_code M)level gb gc gpieces seed K beta geometry ->
 source_ordinary_reflection M(source_L_domain_code M)count phi beta refl ->
 source_finite_telescope M[geometry]refl law ->source_zfr_provable M law.
Proof.
 intros HL HLg HP HPCS HVG HIncluded HG HRefl HLaw.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(source_pcs_table_valid M(source_L_domain_code M)phi count sb sc pieces HD HP HPCS)as HV.
 destruct(source_reflection_geometry_point_total M(source_L_domain_code M)level gb gc gpieces
  (succM M seed)(succM M K)(succM M beta))as(geometryS&HGS).
 destruct(source_LL_instance_total M(succM M beta)(zeroM M))as(lb&HLb).
 assert(PLocal:forall pc body piece wh out,
  source_quantifier_body M phi count pc body ->source_pcs_sign M(source_L_domain_code M)body piece ->
  source_piece_witness_instance M(source_L_domain_code M)pc piece(zeroM M)wh ->
  source_finite_telescope M[geometryS;lb]wh out ->source_descriptor_provable M ZFRSourceDescriptor out).
 { intros pc body piece wh out HBody HSign HWh HTel.
   destruct(pair_total M pc piece)as(entry&HPair).
   assert(HE:context_member M sb sc pieces entry).
   { apply(proj2(HPCS entry)). exists pc,body,piece. auto. }
   apply(proj2(source_zfr_descriptor_provable M out)).
   exact(source_zfr_geometry_piece_witness M(source_L_domain_code M)level gb gc gpieces
    (succM M seed)(succM M K)(succM M beta)(zeroM M)geometryS lb entry pc piece wh out
    HD HL HLg HVG(HIncluded entry HE)HPair HGS HLb HWh HTel). }
 destruct(source_descriptor_tv_witnesses_common_context M ZFRSourceDescriptor(source_L_domain_code M)
  phi count(zeroM M)[geometryS;lb]sb sc pieces HPCS PLocal)as(wb&wc&wn&HWContext&HWitnesses).
 pose proof(proj1(source_zfr_descriptor_context M wb wc wn)HWContext)as HWZFR.
 pose proof(source_zfr_context_closed M wb wc wn HWZFR)as BWClosed.
 destruct(source_zfr_hierarchy_carrier_shell M(succM M beta)(zeroM M))
  as(ordinal&lb'&contained&containLaw&HOrdinal&HLb'&HContained&HContainLaw&ca&cc&cn&HCA&PContain).
 pose proof(source_LL_instance_functional M(succM M beta)(zeroM M)lb lb' HLb HLb')as E. subst lb'.
 pose proof(source_zfr_context_closed M ca cc cn HCA)as BCClosed.
 destruct(context_union_total M wb wc wn ca cc cn)as(ab&ac&an&HUnion).
 pose proof(context_union_left M wb wc wn ca cc cn ab ac an HUnion)as HLeft.
 pose proof(context_union_right M wb wc wn ca cc cn ab ac an HUnion)as HRight.
 assert(HA:source_zfr_context M ab ac an).
 { intros f HF. apply(proj2 HUnion f)in HF. destruct HF as[HF|HF];auto. }
 pose proof(source_zfr_context_closed M ab ac an HA)as BAClosed.
 destruct(source_finite_names_bound M[seed;K;beta])as(k&BN).
 assert(BSeed:coding_lt M seed k)by(apply BN;cbn;tauto).
 assert(BK:coding_lt M K k)by(apply BN;cbn;tauto).
 assert(BBeta:coding_lt M beta k)by(apply BN;cbn;tauto).
 pose proof(source_reflection_geometry_point_bounded M(source_L_domain_code M)level gb gc gpieces
  seed K beta geometry k HD HL HVG BSeed BK BBeta HG)as BGeometry.
 pose proof(source_ordinary_reflection_bounded M(source_L_domain_code M)count phi beta refl k HD HP BBeta HRefl)as BRefl.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k BAClosed(coding_zero_lt_succ M k))as BBase.
 exists ab,ac,an. split;[exact HA|].
 apply(source_full_finite_telescope M[geometry]refl law k).
 - intros f[EF|[]]. now subst f.
 - exact BRefl.
 - exact HLaw.
 - exact BBase.
 - intros b c n BC Included Premises.
   pose proof(Premises geometry(or_introl eq_refl))as PGeometry.
   destruct(context_shift_total M b c n)as(tb&tc&HShift).
   pose proof(context_shift_preserves_bound M b c n tb tc k HShift BC)as BT.
   destruct(environment_cons_total M tb tc n lb)as(ub&uc&un&HCons).
   pose proof(source_LL_instance_bounded M(succM M beta)(zeroM M)lb(succM M k)
    (proj2(coding_lt_succ_cancel M beta k)BBeta)(coding_zero_lt_succ M k)HLb)as BLb.
   pose proof(proj2(context_bounded_cons M tb tc n lb ub uc un(succM M k)HCons)(conj BLb BT))as BU.
   assert(SGeometry:source_formula_shift M geometry geometryS).
   { apply(source_reflection_geometry_point_renaming M(source_L_domain_code M)level gb gc gpieces seed K beta geometry
      (succM M seed)(succM M K)(succM M beta)geometryS(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      HD HL HVG HG HGS);apply(proj2(context_shift_lookup M _ _));reflexivity. }
   pose proof(source_full_prv_shift_cons M b c n tb tc ub uc un lb geometry geometryS(succM M k)
    HShift HCons BU SGeometry PGeometry)as PGeometryS.
   pose proof(source_full_cons_head M tb tc n lb ub uc un(succM M k)HCons BLb BU)as PLb.
   assert(HWIncl:context_included M wb wc wn b c n).
   { intros f HF. exact(Included f(HLeft f HF)). }
   pose proof(source_context_included_shift M wb wc wn b c n wb wc tb tc HWIncl
    (source_closed_context_shift_self M wb wc wn BWClosed)HShift)as HWT.
   assert(HWU:context_included M wb wc wn ub uc un).
   { intros f HF. exact(source_cons_tail_inclusion M tb tc n lb ub uc un HCons f(HWT f HF)). }
   assert(PA:forall a,In a[geometryS;lb] ->source_full_prv M ub uc un a).
   { intros a[EA|[EA|[]]];subst a;assumption. }
   pose proof(HWitnesses ub uc un(succM M k)HWU BU PA)as HW.
   assert(HCIncl:context_included M ca cc cn b c n).
   { intros f HF. exact(Included f(HRight f HF)). }
   pose proof(source_context_included_shift M ca cc cn b c n ca cc tb tc HCIncl
    (source_closed_context_shift_self M ca cc cn BCClosed)HShift)as HCT.
   assert(HCU:context_included M ca cc cn ub uc un).
   { intros f HF. exact(source_cons_tail_inclusion M tb tc n lb ub uc un HCons f(HCT f HF)). }
   pose proof(source_full_prv_weaken_bounded M ca cc cn ub uc un containLaw(succM M k)PContain HCU BU)as PContainU.
   destruct(source_full_reflection_geometry_point_facts M(source_L_domain_code M)level gb gc gpieces
    (succM M seed)(succM M K)(succM M beta)geometryS ub uc un HGS PGeometryS)
    as(m&o&kf&u&ob&l&mb&s&HM&HO&HKF&HU&HOB&HLim&HMB&HS&PM&PO&PKF&PU&POB&PLim&PMB&PS).
   pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(succM M beta)ob ordinal HOB HOrdinal)as E.
   subst ob.
   assert(PC:source_full_prv M ub uc un contained).
   { apply(source_full_finite_telescope_apply M[ordinal;lb]contained containLaw HContainLaw ub uc un PContainU).
     intros a[EA|[EA|[]]];subst a;assumption. }
   assert(HC:source_tv_containment M(source_L_domain_code M)(zeroM M)ub uc un).
   { exists contained. split;[exact HContained|exact PC]. }
   exact(source_full_ordinary_reflection_from_tv M(source_L_domain_code M)phi count beta refl lb
    b c n tb tc ub uc un k HD HP BC BBeta HRefl HLb HShift HCons HW HC).
Qed.

Print Assumptions source_zfr_geometry_ordinary_reflection_over_table.
