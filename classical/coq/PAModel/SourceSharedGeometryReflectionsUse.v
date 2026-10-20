(** Apply both actual shared-geometry reflection laws in an ordinary
 source context, retaining the ordinal and seed-member geometry projections. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourcePCSTables SourcePieceConjunctionBounds
 SourceHierarchySyntax SourceLFixed SourceOrdinaryReflectionSyntax SourceReflectionGeometryPoint SourceReflectionGeometryElimination
 SourceSharedGeometryTwoReflections SourceFiniteTelescope SourceZFRProvability NumericalInstantiation SourceOrdinalPredicate
 NumericalContexts NumericalSourceFull ContextCombination SourceTraceBounds SourceClosedContextShift SourceProofWeakening
 SourceConjunctionRules SourceDerivedRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_full_shared_geometry_reflections M level sb sc pieces pb pc pn qb qc qn phi pcount psi qcount seed K beta
 geometry reflP reflQ ordinal member gb gc gn k:
 source_bounded M level(code_numeral M 2)->source_LL_instance M(code_numeral M 1)(zeroM M)level->
 source_bounded M phi pcount->source_pcs_table M(source_L_domain_code M)phi pcount pb pc pn->
 source_bounded M psi qcount->source_pcs_table M(source_L_domain_code M)psi qcount qb qc qn->
 source_piece_table_valid M sb sc pieces->context_included M pb pc pn sb sc pieces->context_included M qb qc qn sb sc pieces->
 source_reflection_geometry_point M(source_L_domain_code M)level sb sc pieces seed K beta geometry->
 source_ordinary_reflection M(source_L_domain_code M)pcount phi beta reflP->source_ordinary_reflection M(source_L_domain_code M)qcount psi beta reflQ->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->sf_relation M SFMember seed beta member->
 context_bounded M gb gc gn k->source_full_prv M gb gc gn geometry->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un reflP /\source_full_prv M ub uc un reflQ /\
 source_full_prv M ub uc un ordinal /\source_full_prv M ub uc un member.
Proof.
 intros BL HL BP HPT BQ HQT HV HPIn HQIn HG HRP HRQ HO HM BC PG.
 destruct(sf_relation_total M SFAnd reflP reflQ)as(pair&HPair).
 destruct(sf_relation_total M SFImpl geometry pair)as(law&HImpl).
 assert(HT:source_finite_telescope M[geometry]pair law)by(exists pair;split;[reflexivity|exact HImpl]).
 destruct(source_zfr_geometry_two_reflections M level sb sc pieces pb pc pn qb qc qn phi pcount psi qcount seed K beta
  geometry reflP reflQ pair law BL HL BP HPT BQ HQT HV HPIn HQIn HG HRP HRQ HPair HT)as(nb&nc&nn&HNC&PLaw).
 destruct(context_union_total M gb gc gn nb nc nn)as(ub&uc&un&HU).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)
  (coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 assert(HWeaken:forall f,source_full_prv M gb gc gn f->source_full_prv M ub uc un f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn ub uc un f k PF
   (context_union_left M gb gc gn nb nc nn ub uc un HU)BU). }
 pose proof(source_full_prv_weaken_bounded M nb nc nn ub uc un law k PLaw
  (context_union_right M gb gc gn nb nc nn ub uc un HU)BU)as PLawU.
 pose proof(source_full_modus_ponens M ub uc un geometry pair law HImpl PLawU(HWeaken _ PG))as PPair.
 destruct(source_full_reflection_geometry_point_facts M(source_L_domain_code M)level sb sc pieces seed K beta geometry gb gc gn HG PG)
  as(m&o&kf&u&ob&lim&mb&s&Hm&Ho&Hkf&Hu&Hob&Hlim&Hmb&Hs&Pm&Po&Pkf&Pu&Pob&Plim&Pmb&Ps).
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)beta ob ordinal Hob HO)as E;subst ob.
 pose proof(sf_relation_functional M SFMember seed beta mb member Hmb HM)as E;subst mb.
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|]. split.
 - exact(source_full_conjunction_left M ub uc un reflP reflQ pair HPair PPair).
 - split;[exact(source_full_conjunction_right M ub uc un reflP reflQ pair HPair PPair)|]. split;apply HWeaken;assumption.
Qed.
Print Assumptions source_full_shared_geometry_reflections.
