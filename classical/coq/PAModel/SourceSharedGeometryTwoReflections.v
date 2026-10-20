(** Actual simultaneous reflection of two arbitrary internal matrices
 from one common valid PCS geometry. No conjunct-reflection principle is used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePCSTables SourcePieceConjunctionBounds SourceHierarchySyntax SourceLFixed SourceOrdinaryReflectionSyntax
 SourceReflectionGeometryPoint SourceSharedGeometryReflection SourceZFRProvability SourceFiniteTelescope
 SourceFiniteFamilyBounds ContextCombination NumericalContexts NumericalSourceFull SourceTraceBounds
 SourceClosedContextShift SourceProofWeakening SourceConjunctionRules SourceDerivedRules SourceUpperProofHelpers.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_geometry_two_reflections M level gb gc gn pb pc pn qb qc qn phi pcount psi qcount seed K beta
 geometry reflP reflQ pair law:
 source_bounded M level(code_numeral M 2)->source_LL_instance M(code_numeral M 1)(zeroM M)level->
 source_bounded M phi pcount->source_pcs_table M(source_L_domain_code M)phi pcount pb pc pn->
 source_bounded M psi qcount->source_pcs_table M(source_L_domain_code M)psi qcount qb qc qn->
 source_piece_table_valid M gb gc gn->context_included M pb pc pn gb gc gn->context_included M qb qc qn gb gc gn->
 source_reflection_geometry_point M(source_L_domain_code M)level gb gc gn seed K beta geometry->
 source_ordinary_reflection M(source_L_domain_code M)pcount phi beta reflP->
 source_ordinary_reflection M(source_L_domain_code M)qcount psi beta reflQ->
 sf_relation M SFAnd reflP reflQ pair->source_finite_telescope M[geometry]pair law->source_zfr_provable M law.
Proof.
 intros BL HLevel BP HPT BQ HQT HV HPIn HQIn HG HRP HRQ HPair HLaw.
 destruct(sf_relation_total M SFImpl geometry reflP)as(lawP&HLP).
 destruct(sf_relation_total M SFImpl geometry reflQ)as(lawQ&HLQ).
 assert(TP:source_finite_telescope M[geometry]reflP lawP)by(exists reflP;split;[reflexivity|exact HLP]).
 assert(TQ:source_finite_telescope M[geometry]reflQ lawQ)by(exists reflQ;split;[reflexivity|exact HLQ]).
 destruct(source_zfr_geometry_ordinary_reflection_over_table M level gb gc gn pb pc pn phi pcount seed K beta
  geometry reflP lawP BL HLevel BP HPT HV HPIn HG HRP TP)as(ab&ac&an&HAC&PP).
 destruct(source_zfr_geometry_ordinary_reflection_over_table M level gb gc gn qb qc qn psi qcount seed K beta
  geometry reflQ lawQ BL HLevel BQ HQT HV HQIn HG HRQ TQ)as(bb&bc&bn&HBC&PQ).
 destruct(context_union_total M ab ac an bb bc bn)as(nb&nc&nn&HU).
 assert(HNC:source_zfr_context M nb nc nn).
 { intros a HA. apply(proj1(proj2 HU a))in HA. destruct HA as[HA|HA];[exact(HAC a HA)|exact(HBC a HA)]. }
 destruct(source_finite_names_bound M[seed;K;beta])as(k&HNames).
 assert(BSeed:coding_lt M seed k)by(apply HNames;cbn;tauto).
 assert(BK:coding_lt M K k)by(apply HNames;cbn;tauto).
 assert(BBeta:coding_lt M beta k)by(apply HNames;cbn;tauto).
 pose proof(source_reflection_geometry_point_bounded M(source_L_domain_code M)level gb gc gn seed K beta geometry k
  (numerical_L_domain_bounded M)BL HV BSeed BK BBeta HG)as BG.
 pose proof(source_ordinary_reflection_bounded M(source_L_domain_code M)pcount phi beta reflP k
  (numerical_L_domain_bounded M)BP BBeta HRP)as BRP.
 pose proof(source_ordinary_reflection_bounded M(source_L_domain_code M)qcount psi beta reflQ k
  (numerical_L_domain_bounded M)BQ BBeta HRQ)as BRQ.
 pose proof(proj2(source_bounded_accept_binary M SFAnd reflP reflQ pair k(or_introl eq_refl)HPair)(conj BRP BRQ))as BPair.
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)
  (coding_zero_lt_succ M k))as BN.
 exists nb,nc,nn. split;[exact HNC|].
 apply(source_full_finite_telescope M[geometry]pair law k).
 - intros f[<-|[]]. exact BG.
 - exact BPair.
 - exact HLaw.
 - exact BN.
 - intros tb tc tn BT HIncluded HPremises.
   assert(HLeft:context_included M ab ac an tb tc tn).
   { intros a HA. apply HIncluded. exact(context_union_left M ab ac an bb bc bn nb nc nn HU a HA). }
   assert(HRight:context_included M bb bc bn tb tc tn).
   { intros a HA. apply HIncluded. exact(context_union_right M ab ac an bb bc bn nb nc nn HU a HA). }
   pose proof(source_full_prv_weaken_bounded M ab ac an tb tc tn lawP k PP HLeft BT)as PP'.
   pose proof(source_full_prv_weaken_bounded M bb bc bn tb tc tn lawQ k PQ HRight BT)as PQ'.
   pose proof(HPremises geometry(or_introl eq_refl))as PG.
   exact(source_full_conjunction M tb tc tn reflP reflQ pair HPair
    (source_full_modus_ponens M tb tc tn geometry reflP lawP HLP PP' PG)
    (source_full_modus_ponens M tb tc tn geometry reflQ lawQ HLQ PQ' PG)).
Qed.
Print Assumptions source_zfr_geometry_two_reflections.
