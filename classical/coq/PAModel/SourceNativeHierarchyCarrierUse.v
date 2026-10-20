(** Actual ordinal hierarchy witnesses supply both constructibility of
 the carrier and constructibility of each of its elements. No carrier-domain
 or element-containment law remains an assumption of the native proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceLFixed
 SourceHierarchySyntax SourceHierarchyCarrierContained SourceLLevelShell SourceDomainCarrierTransport SourceOrdinalPredicate
 SourceFiniteTelescope SourceZFRProvability NumericalInstantiation NumericalContexts NumericalSourceFull ContextCombination
 SourceTraceBounds SourceClosedContextShift SourceProofWeakening SourceDerivedRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma source_native_domain_carrier_functional M domain Y a b:
 source_domain_carrier M domain Y a->source_domain_carrier M domain Y b->a=b.
Proof.
 intros(g&p&HG&HP&HA)(g'&p'&HG'&HP'&HB).
 pose proof(sf_relation_functional M SFMember(zeroM M)(succM M Y)g g' HG HG')as E;subst g'.
 pose proof(sf_relation_functional M SFImpl g domain p p' HP HP')as E;subst p'.
 exact(sf_relation_functional M SFAll p(zeroM M)a b HA HB).
Qed.
Theorem source_full_native_hierarchy_carrier M beta Y ordinal level carrier_domain contained gb gc gn k:
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->source_LL_instance M beta Y level->
 numerical_instantiation M(source_L_domain_code M)Y carrier_domain->source_domain_carrier M(source_L_domain_code M)Y contained->
 context_bounded M gb gc gn k->source_full_prv M gb gc gn ordinal->source_full_prv M gb gc gn level->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un carrier_domain /\source_full_prv M ub uc un contained.
Proof.
 intros HO HL HD HC BC PO PL.
 destruct(source_zfr_hierarchy_carrier_shell M beta Y)as(o&l&contained'&lawC&HO'&HL'&HC'&HT&PC).
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)beta o ordinal HO' HO)as E;subst o.
 pose proof(source_LL_instance_functional M beta Y l level HL' HL)as E;subst l.
 change(source_domain_carrier M(source_L_domain_code M)Y contained')in HC'.
 pose proof(source_native_domain_carrier_functional M(source_L_domain_code M)Y contained' contained HC' HC)as E;subst contained'.
 destruct(source_zfr_L_level_shell M beta Y)as(o&l&d&tail&lawD&HOD&HLD&HDD&HI&HOI&PD).
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)beta o ordinal HOD HO)as E;subst o.
 pose proof(source_LL_instance_functional M beta Y l level HLD HL)as E;subst l.
 pose proof(numerical_instantiation_functional M(source_L_domain_code M)Y d carrier_domain HDD HD)as E;subst d.
 destruct PC as(cb&cc&cn&HCC&PC),PD as(db&dc&dn&HDC&PD).
 destruct(context_union_total M cb cc cn db dc dn)as(nb&nc&nn&HN).
 assert(HNC:source_zfr_context M nb nc nn).
 { intros a HA. apply(proj1(proj2 HN a))in HA. destruct HA as[HA|HA];[exact(HCC a HA)|exact(HDC a HA)]. }
 destruct(context_union_total M gb gc gn nb nc nn)as(ub&uc&un&HU).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)
  (coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 assert(HWeaken:forall f,source_full_prv M gb gc gn f->source_full_prv M ub uc un f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn ub uc un f k PF
   (context_union_left M gb gc gn nb nc nn ub uc un HU)BU). }
 assert(HCIn:context_included M cb cc cn ub uc un).
 { intros a HA. apply(context_union_right M gb gc gn nb nc nn ub uc un HU).
   exact(context_union_left M cb cc cn db dc dn nb nc nn HN a HA). }
 assert(HDIn:context_included M db dc dn ub uc un).
 { intros a HA. apply(context_union_right M gb gc gn nb nc nn ub uc un HU).
   exact(context_union_right M cb cc cn db dc dn nb nc nn HN a HA). }
 pose proof(source_full_prv_weaken_bounded M cb cc cn ub uc un lawC k PC HCIn BU)as PCU.
 pose proof(source_full_prv_weaken_bounded M db dc dn ub uc un lawD k PD HDIn BU)as PDU.
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|]. split.
 - exact(source_full_modus_ponens M ub uc un level carrier_domain tail HI
    (source_full_modus_ponens M ub uc un ordinal tail lawD HOI PDU(HWeaken _ PO))(HWeaken _ PL)).
 - apply(source_full_finite_telescope_apply M[ordinal;level]contained lawC HT ub uc un PCU).
   intros a[<-|[<-|[]]];apply HWeaken;assumption.
Qed.
Print Assumptions source_native_domain_carrier_functional.
Print Assumptions source_full_native_hierarchy_carrier.
