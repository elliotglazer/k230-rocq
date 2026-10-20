(** Literal existence of an ordinal limit reflecting an arbitrary internal
    matrix, retaining membership of a supplied ordinal. This is syntax only. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalInstantiation SourceOrdinalPredicate SourceDomainInstances SourceReflectionGeometryPredicates
 SourceOrdinaryReflectionSyntax.
Unset Implicit Arguments.
Definition source_ordinary_reflection_point M domain count phi seed beta out:=exists ordinal limit member refl tail middle,
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\
 source_reflection_geometry_instance M ReflectionLimit(fun _=>beta)limit /\
 sf_relation M SFMember seed beta member /\source_ordinary_reflection M domain count phi beta refl /\
 sf_relation M SFAnd member refl tail /\sf_relation M SFAnd limit tail middle /\sf_relation M SFAnd ordinal middle out.
Definition source_ordinary_reflection_exists M domain count phi seed out:=exists point,
 source_ordinary_reflection_point M domain count phi(succM M seed)(zeroM M)point /\
 sf_relation M SFEx point(zeroM M)out.
Theorem source_ordinary_reflection_point_total M domain count phi seed beta:
 exists out,source_ordinary_reflection_point M domain count phi seed beta out.
Proof.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)beta)as(ordinal&HO).
 destruct(source_reflection_geometry_instance_total M ReflectionLimit(fun _=>beta))as(limit&HL).
 destruct(sf_relation_total M SFMember seed beta)as(member&HM).
 destruct(source_ordinary_reflection_total M domain count phi beta)as(refl&HR).
 destruct(sf_relation_total M SFAnd member refl)as(tail&HT).
 destruct(sf_relation_total M SFAnd limit tail)as(middle&HMid).
 destruct(sf_relation_total M SFAnd ordinal middle)as(out&HOut).
 exists out,ordinal,limit,member,refl,tail,middle. do 6(split;[assumption|]). exact HOut.
Qed.
Theorem source_ordinary_reflection_exists_total M domain count phi seed:
 exists out,source_ordinary_reflection_exists M domain count phi seed out.
Proof.
 destruct(source_ordinary_reflection_point_total M domain count phi(succM M seed)(zeroM M))as(point&HP).
 destruct(sf_relation_total M SFEx point(zeroM M))as(out&HO).
 exists out,point. auto.
Qed.
Theorem source_ordinary_reflection_point_bounded M domain count phi seed beta out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 coding_lt M seed k ->coding_lt M beta k ->source_ordinary_reflection_point M domain count phi seed beta out ->
 source_bounded M out k.
Proof.
 intros HD HP BS BB(ordinal&limit&member&refl&tail&middle&HO&HL&HM&HR&HT&HMid&HOut).
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ordinal k
  (source_ordinal_predicate_bounded M)BB HO)as BO.
 assert(BL:source_bounded M limit k).
 { apply(source_reflection_geometry_instance_bounded M ReflectionLimit(fun _=>beta)limit k);[intros;exact BB|exact HL]. }
 pose proof(proj2(source_bounded_accept_atom M SFMember seed beta member k(or_introl eq_refl)HM)(conj BS BB))as BM.
 pose proof(source_ordinary_reflection_bounded M domain count phi beta refl k HD HP BB HR)as BR.
 pose proof(proj2(source_bounded_accept_binary M SFAnd member refl tail k(or_introl eq_refl)HT)(conj BM BR))as BT.
 pose proof(proj2(source_bounded_accept_binary M SFAnd limit tail middle k(or_introl eq_refl)HMid)(conj BL BT))as BMid.
 exact(proj2(source_bounded_accept_binary M SFAnd ordinal middle out k(or_introl eq_refl)HOut)(conj BO BMid)).
Qed.
Theorem source_ordinary_reflection_exists_bounded M domain count phi seed out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->coding_lt M seed k ->
 source_ordinary_reflection_exists M domain count phi seed out ->source_bounded M out k.
Proof.
 intros HD HP BS(point&HPoint&HEx).
 apply(proj2(source_bounded_accept_unary M SFEx point out k(or_intror eq_refl)HEx)).
 exact(source_ordinary_reflection_point_bounded M domain count phi(succM M seed)(zeroM M)point(succM M k)
  HD HP(proj2(coding_lt_succ_cancel M seed k)BS)(coding_zero_lt_succ M k)HPoint).
Qed.
Print Assumptions source_ordinary_reflection_point_total.
Print Assumptions source_ordinary_reflection_exists_total.
Print Assumptions source_ordinary_reflection_point_bounded.
Print Assumptions source_ordinary_reflection_exists_bounded.
