(** Ordinary reflected witness requests yield the literal domain-relative
 native witness_closed formula, with both domain guards proved explicitly. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 SourceBounded SourceRelativizationBounds SourceUpperWitnessRecipes SourceReflectedRequestLink SourceNativeRelativeRequest
 SourceDomainCarrierTransport SourceRelativization SourceRelativizationRules SourceRelativizationFunctionality
 SourcePropositionalRebase NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull
 SourceQuantifierRules SourceProofRenaming SourceContextProofHelpers SourceUniversalPropositional SourceDerivedRules.
Unset Implicit Arguments.
Definition source_native_reflected_witness_closed M domain carrier matrix out:=exists guard reflected point,
 sf_relation M SFMember(zeroM M)(succM M carrier)guard /\
 source_reflected_request_recipe M domain(succM M carrier)matrix reflected /\
 sf_relation M SFImpl guard reflected point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_upper_matrix_request_graph_intro M matrix carrier member pair some bounded request:
 sf_relation M SFMember(zeroM M)(succM M carrier)member ->sf_relation M SFAnd member matrix pair ->
 sf_relation M SFEx matrix(zeroM M)some ->sf_relation M SFEx pair(zeroM M)bounded ->sf_relation M SFImpl some bounded request ->
 code_relation M(schema_env3 matrix carrier carrier)(E_upper_matrix_request(CEvar 0)(CEvar 1))request.
Proof.
 intros HM HP HS HB HR. set(rho:=schema_env3 matrix carrier carrier).
 pose proof(proj2(schema_expression_graph M rho SFMember(CEconst 0)(CEadd(CEvar 1)(CEconst 1))(zeroM M)(succM M carrier)member eq_refl(source_name_plus_one_graph M matrix carrier))HM)as HMG.
 pose proof(proj2(schema_expression_graph M rho SFAnd _ (CEvar 0)member matrix pair HMG eq_refl)HP)as HPG.
 pose proof(proj2(schema_expression_graph M rho SFEx(CEvar 0)(CEconst 0)matrix(zeroM M)some eq_refl eq_refl)HS)as HSG.
 pose proof(proj2(schema_expression_graph M rho SFEx _ (CEconst 0)pair(zeroM M)bounded HPG eq_refl)HB)as HBG.
 exact(proj2(schema_expression_graph M rho SFImpl _ _ some bounded request HSG HBG)HR).
Qed.
Theorem source_full_native_relative_witness_closed M domain carrier matrix raw reflectedAll contained relative gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M matrix(succM M(succM M k)) ->coding_lt M carrier k ->context_bounded M gb gc gn k ->
 code_relation M(schema_env3 matrix carrier carrier)(E_upper_witness_closed(CEvar 0)(CEvar 1))raw ->
 source_native_reflected_witness_closed M domain carrier matrix reflectedAll ->source_domain_carrier M domain carrier contained ->
 source_relativization M domain raw relative ->source_full_prv M gb gc gn reflectedAll ->source_full_prv M gb gc gn contained ->
 source_full_prv M gb gc gn relative.
Proof.
 intros HD BM HY BC HRaw(g&reflected&refPoint&HG&HReflected&HRefPoint&HRefAll)HContained HRelative PRefAll PContained.
 destruct(source_upper_witness_closed_shell M matrix carrier raw HRaw)as(guard&member&pair&some&bounded&request&point&HGuard&HMember&HPair&HSome&HBounded&HRequest&HPoint&HAll).
 assert(E:guard=g)by(eapply sf_relation_functional;eassumption). subst guard.
 pose proof(source_upper_matrix_request_graph_intro M matrix(succM M carrier)member pair some bounded request HMember HPair HSome HBounded HRequest)as HRawRequest.
 destruct(source_relativization_total M domain request)as(relativeRequest&HRR).
 destruct(sf_relation_total M SFImpl g relativeRequest)as(relativePoint&HRPoint).
 destruct(sf_relation_total M SFImpl domain relativePoint)as(domainPoint&HDP).
 destruct(sf_relation_total M SFAll domainPoint(zeroM M))as(relativeWhole&HRAll).
 assert(HRBody:source_relativization M domain point relativePoint).
 { exact(source_relativization_binary M domain SFImpl g request point g relativeRequest relativePoint(or_intror(or_intror eq_refl))HPoint
   (source_relativization_atom M domain SFMember(zeroM M)(succM M carrier)g(or_introl eq_refl)HG)HRR HRPoint). }
 assert(HRWhole:source_relativization M domain raw relativeWhole).
 { apply(source_relativization_quantifier M domain true point raw relativePoint relativeWhole HAll HRBody). exists domainPoint. auto. }
 assert(E:relativeWhole=relative)by(eapply source_relativization_functional;eassumption). subst relativeWhole.
 assert(BG:source_bounded M g(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)g(succM M k)(or_introl eq_refl)HG)).
   exact(conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M carrier k)HY)). }
 assert(BMember:source_bounded M member(succM M(succM M k))).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M(succM M carrier))member(succM M(succM M k))(or_introl eq_refl)HMember)).
   exact(conj(coding_zero_lt_succ M(succM M k))(proj2(coding_lt_succ_cancel M(succM M carrier)(succM M k))(proj2(coding_lt_succ_cancel M carrier k)HY))). }
 pose proof(proj2(source_bounded_accept_binary M SFAnd member matrix pair(succM M(succM M k))(or_introl eq_refl)HPair)(conj BMember BM))as BPair.
 pose proof(proj2(source_bounded_accept_unary M SFEx matrix some(succM M k)(or_intror eq_refl)HSome)BM)as BSome.
 pose proof(proj2(source_bounded_accept_unary M SFEx pair bounded(succM M k)(or_intror eq_refl)HBounded)BPair)as BBounded.
 pose proof(proj2(source_bounded_accept_binary M SFImpl some bounded request(succM M k)(or_intror(or_intror eq_refl))HRequest)(conj BSome BBounded))as BRequest.
 pose proof(proj2(source_bounded_accept_binary M SFImpl g request point(succM M k)(or_intror(or_intror eq_refl))HPoint)(conj BG BRequest))as BPoint.
 pose proof(proj2(source_bounded_accept_unary M SFAll point raw k(or_introl eq_refl)HAll)BPoint)as BRaw.
 pose proof(source_relativization_preserves_bound M raw domain k relative HD BRaw HRelative)as BRelative.
 pose proof(proj1(source_bounded_accept_unary M SFAll domainPoint relative k(or_introl eq_refl)HRAll)BRelative)as BDomainPoint.
 pose proof(proj2(proj1(source_bounded_accept_binary M SFImpl domain relativePoint domainPoint(succM M k)(or_intror(or_intror eq_refl))HDP)BDomainPoint))as BRelativePoint.
 pose proof(sr_domain_bound_succ M domain k HD)as BDomain.
 destruct(context_shift_total M gb gc gn)as(sb&sc&HShift).
 pose proof(context_shift_preserves_bound M gb gc gn sb sc k HShift BC)as BS.
 pose proof(source_full_all_shift M gb gc gn refPoint reflectedAll sb sc HRefAll PRefAll HShift)as PRefPoint.
 destruct(source_domain_carrier_total M domain(succM M carrier))as(containedS&HContainedS).
 pose proof(source_domain_carrier_shift M domain carrier contained containedS HD HContained HContainedS)as HSContained.
 pose proof(source_full_prv_renaming M gb gc gn contained(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc containedS PContained HShift HSContained)as PContainedS.
 destruct HContainedS as(memberD&pointD&HMemberD&HPointD&HAllD).
 destruct(environment_cons_total M sb sc gn domain)as(db&dc&dn&HDomainCons).
 pose proof(proj2(context_bounded_cons M sb sc gn domain db dc dn(succM M k)HDomainCons)(conj BDomain BS))as BD.
 destruct(environment_cons_total M db dc dn g)as(ub&uc&un&HGuardCons).
 pose proof(proj2(context_bounded_cons M db dc dn g ub uc un(succM M k)HGuardCons)(conj BG BD))as BU.
 pose proof(source_full_cons_head M db dc dn g ub uc un(succM M k)HGuardCons BG BU)as PG.
 pose proof(source_full_cons_weaken M sb sc gn domain db dc dn(succM M k)refPoint HDomainCons BD PRefPoint)as PR1.
 pose proof(source_full_cons_weaken M db dc dn g ub uc un(succM M k)refPoint HGuardCons BU PR1)as PR2.
 pose proof(source_full_modus_ponens M ub uc un g reflected refPoint HRefPoint PR2 PG)as PReflected.
 pose proof(source_full_cons_weaken M sb sc gn domain db dc dn(succM M k)containedS HDomainCons BD PContainedS)as PC1.
 pose proof(source_full_cons_weaken M db dc dn g ub uc un(succM M k)containedS HGuardCons BU PC1)as PC2.
 pose proof(source_full_native_relative_matrix_request M domain(succM M carrier)matrix request reflected relativeRequest memberD pointD containedS ub uc un(succM M k)
  HD BM(proj2(coding_lt_succ_cancel M carrier k)HY)BU HRawRequest HReflected HRR HMemberD HPointD HAllD PReflected PC2)as PRelativeRequest.
 apply(full_source_AllI M gb gc gn domainPoint relative sb sc(ex_intro _ k(conj BRelative BC)));[|exact HShift|exact HRAll].
 apply(full_source_II M sb sc gn domain relativePoint domainPoint db dc dn(ex_intro _ (succM M k)(conj BDomainPoint BS)));[|exact HDomainCons|exact HDP].
 apply(full_source_II M db dc dn g relativeRequest relativePoint ub uc un(ex_intro _ (succM M k)(conj BRelativePoint BD)));[exact PRelativeRequest|exact HGuardCons|exact HRPoint].
Qed.
Print Assumptions source_upper_matrix_request_graph_intro.
Print Assumptions source_full_native_relative_witness_closed.
