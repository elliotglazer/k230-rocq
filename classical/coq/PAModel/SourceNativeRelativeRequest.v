(** Exact native matrix-request image from ordinary reflected witnesses
 and genuine carrier containment in the relativizing domain. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
 SourceBounded SourceRelativizationBounds NumericalContexts NumericalSourceFull
 SourceUpperWitnessRecipes SourceReflectedRequestLink SourceReflectedRequestDomainGuard
 SourceRelativization SourceRelativizationRules SourceRelativizationFunctionality SourceSetRelativizationRules.
Unset Implicit Arguments.
Theorem source_full_native_relative_matrix_request M domain carrier matrix raw reflected relative guard point all gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M matrix(succM M k) ->coding_lt M carrier k ->context_bounded M gb gc gn k ->
 code_relation M(schema_env3 matrix carrier carrier)(E_upper_matrix_request(CEvar 0)(CEvar 1))raw ->
 source_reflected_request_recipe M domain carrier matrix reflected ->source_relativization M domain raw relative ->
 sf_relation M SFMember(zeroM M)(succM M carrier)guard ->sf_relation M SFImpl guard domain point ->sf_relation M SFAll point(zeroM M)all ->
 source_full_prv M gb gc gn reflected ->source_full_prv M gb gc gn all ->source_full_prv M gb gc gn relative.
Proof.
 intros HD HM HY BC HRaw(left&some&bounded&HLeft&HSome&HBounded&HReflected)HRelative HGuard HPoint HAll PReflected PAll.
 destruct(source_upper_matrix_request_shell M matrix carrier raw HRaw)as(rawmember&rawpair&rawsome&rawbounded&HRM&HRPair&HRawSome&HRawBounded&HRawImpl).
 assert(EGuard:rawmember=guard)by(eapply sf_relation_functional;eassumption). subst rawmember.
 destruct HBounded as(member&oldBody&HMember&HOldBody&HBounded).
 assert(EGuard:member=guard)by(eapply sf_relation_functional;eassumption). subst member.
 destruct(sf_relation_total M SFAnd domain oldBody)as(newBody&HNewBody).
 destruct(sf_relation_total M SFEx newBody(zeroM M))as(newEx&HNewEx).
 destruct(sf_relation_total M SFImpl some newEx)as(guardedRequest&HGuardedRequest).
 assert(HSomeRel:source_relativization M domain rawsome some).
 { exact(source_relativization_quantifier M domain false matrix rawsome left some HRawSome HLeft HSome). }
 assert(HBodyRel:source_relativization M domain rawpair oldBody).
 { exact(source_relativization_binary M domain SFAnd guard matrix rawpair guard left oldBody(or_introl eq_refl)HRPair
   (source_relativization_atom M domain SFMember(zeroM M)(succM M carrier)guard(or_introl eq_refl)HGuard)HLeft HOldBody). }
 assert(HBoundedRel:source_relativization M domain rawbounded newEx).
 { apply(source_relativization_quantifier M domain false rawpair rawbounded oldBody newEx HRawBounded HBodyRel).
   exists newBody. auto. }
 assert(HRequestRel:source_relativization M domain raw guardedRequest).
 { exact(source_relativization_binary M domain SFImpl rawsome rawbounded raw some newEx guardedRequest
   (or_intror(or_intror eq_refl))HRawImpl HSomeRel HBoundedRel HGuardedRequest). }
 assert(E:guardedRequest=relative)by(eapply source_relativization_functional;eassumption). subst relative.
 assert(BGuard:source_bounded M guard(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)guard(succM M k)(or_introl eq_refl)HGuard)).
   exact(conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M carrier k)HY)). }
 pose proof(sr_domain_bound_succ M domain k HD)as BDomain.
 pose proof(source_relativization_preserves_bound M matrix domain(succM M k)left HD HM HLeft)as BLeft.
 destruct HSome as(someBody&HSomeBody&HSomeEx).
 pose proof(proj2(source_bounded_accept_binary M SFAnd domain left someBody(succM M k)(or_introl eq_refl)HSomeBody)(conj BDomain BLeft))as BSomeBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx someBody some k(or_intror eq_refl)HSomeEx)BSomeBody)as BSome.
 exact(source_full_reflected_request_add_domain_guard M gb gc gn k guard domain left oldBody bounded point all newBody newEx some reflected guardedRequest
  BC BGuard BDomain BLeft BSome HOldBody HBounded HPoint HAll HNewBody HNewEx HReflected HGuardedRequest PAll PReflected).
Qed.
Print Assumptions source_full_native_relative_matrix_request.
