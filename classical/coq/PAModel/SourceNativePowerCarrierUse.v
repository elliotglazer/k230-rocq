(** Ordinary source-proof consumer of the actual fixed Power Set selector
 law. It adjoins only an explicitly returned finite ZFR axiom context. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceNativePowerCarrierFixed SourceNativePowerCarrierShell SourceOrdinaryReflectionSyntax
 SourceOrdinalPredicate SourceHierarchySyntax SourceUpperTraceFrame SourceRelativization SourceRelativizationFunctionality
 NumericalInstantiation NumericalContexts NumericalSourceFull ContextCombination SourceZFRProvability
 SourceProofWeakening SourceTraceBounds SourceFiniteTelescope SourceClosedContextShift SourceContextTransport.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma source_cp_telescope_functional M A target old new:
 source_finite_telescope M A target old->source_finite_telescope M A target new->old=new.
Proof.
 revert old new. induction A as[|a A IH];intros old new HT HT'.
 - change(old=target)in HT. change(new=target)in HT'. congruence.
 - destruct HT as(inner&HI&HG),HT' as(inner'&HI'&HG').
   pose proof(IH inner inner' HI HI')as E;subst inner'. exact(sf_relation_functional M SFImpl a inner old new HG HG').
Qed.
Theorem source_native_cp_subset_law M beta Y s t refl ordinal level st sY tY raw relative law:
 source_ordinary_reflection M(SourceLFixed.source_L_domain_code M)(code_numeral M 4)
  (code_numeral M(sf_encode source_native_cp_theta))beta refl->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->source_LL_instance M beta Y level->
 sf_relation M SFMember s t st->sf_relation M SFMember s Y sY->sf_relation M SFMember t Y tY->
 source_subset_closed_graph M Y raw->source_relativization M(SourceLFixed.source_L_domain_code M)raw relative->
 source_finite_telescope M [refl;ordinal;level;st;sY;tY]relative law->source_zfr_provable M law.
Proof.
 intros HR HO HL HST HSY HTY HRaw HRelative HT.
 destruct(source_zfr_native_cp_subset_shell M beta Y s t)as(r'&o'&l'&st'&sy'&ty'&raw'&relative'&law'&HR'&HO'&HL'&HST'&HSY'&HTY'&HRaw'&HRelative'&HT'&PLaw).
 pose proof(source_ordinary_reflection_functional M _ _ _ beta refl r' HR HR')as E;subst r'.
 pose proof(numerical_instantiation_functional M _ beta ordinal o' HO HO')as E;subst o'.
 pose proof(source_LL_instance_functional M beta Y level l' HL HL')as E;subst l'.
 pose proof(sf_relation_functional M SFMember s t st st' HST HST')as E;subst st'.
 pose proof(sf_relation_functional M SFMember s Y sY sy' HSY HSY')as E;subst sy'.
 pose proof(sf_relation_functional M SFMember t Y tY ty' HTY HTY')as E;subst ty'.
 pose proof(code_relation_functional M _ _ raw raw' HRaw HRaw')as E;subst raw'.
 pose proof(source_relativization_functional M raw(SourceLFixed.source_L_domain_code M)relative relative' HRelative HRelative')as E;subst relative'.
 pose proof(source_cp_telescope_functional M _ relative law law' HT HT')as E.
 now subst law'.
Qed.
Theorem source_full_native_cp_subset M beta Y s t refl ordinal level st sY tY raw relative gb gc gn k:
 context_bounded M gb gc gn k->
 source_ordinary_reflection M(SourceLFixed.source_L_domain_code M)(code_numeral M 4)
  (code_numeral M(sf_encode source_native_cp_theta))beta refl->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->source_LL_instance M beta Y level->
 sf_relation M SFMember s t st->sf_relation M SFMember s Y sY->sf_relation M SFMember t Y tY->
 source_subset_closed_graph M Y raw->source_relativization M(SourceLFixed.source_L_domain_code M)raw relative->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn ordinal->source_full_prv M gb gc gn level->
 source_full_prv M gb gc gn st->source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\
  context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un relative.
Proof.
 intros BC HR HO HL HST HSY HTY HRaw HRelative PR PO PL PST PSY PTY.
 destruct(source_finite_telescope_total M [refl;ordinal;level;st;sY;tY]relative)as(law&HT).
 destruct(source_native_cp_subset_law M beta Y s t refl ordinal level st sY tY raw relative law
  HR HO HL HST HSY HTY HRaw HRelative HT)as(nb&nc&nn&HNC&PLaw).
 destruct(context_union_total M gb gc gn nb nc nn)as(ub&uc&un&HU).
 pose proof(source_zfr_context_closed M nb nc nn HNC)as BN0.
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k BN0(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 pose proof(source_full_prv_weaken_bounded M nb nc nn ub uc un law k PLaw
  (context_union_right M gb gc gn nb nc nn ub uc un HU)BU)as PNewLaw.
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|].
 apply(source_full_finite_telescope_apply M [refl;ordinal;level;st;sY;tY]relative law HT ub uc un PNewLaw).
 assert(HWeaken:forall f,source_full_prv M gb gc gn f->source_full_prv M ub uc un f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn ub uc un f k PF
    (context_union_left M gb gc gn nb nc nn ub uc un HU)BU). }
 intros a HA. simpl in HA. destruct HA as[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];apply HWeaken;assumption.
Qed.
Print Assumptions source_native_cp_subset_law.
Print Assumptions source_full_native_cp_subset.
