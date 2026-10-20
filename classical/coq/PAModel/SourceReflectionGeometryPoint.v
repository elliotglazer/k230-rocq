(** The exact two-witness geometry payload retained for final reflection. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
 SourceCofinalGeometry SourceReflectionKF SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations
 SourceOrdinalPredicate SourceDomainInstances SourcePieceConjunctionBounds SourcePropositionalTemplates.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition source_reflection_geometry_payload:=SPTAnd(SPTSlot 0)(SPTAnd(SPTSlot 1)(SPTAnd(SPTSlot 2)(SPTAnd(SPTSlot 3)(SPTAnd(SPTSlot 4)(SPTAnd(SPTSlot 5)(SPTAnd(SPTSlot 6)(SPTSlot 7))))))).
Definition source_reflection_geometry_values {A:Type}(a b c d e f g h:A)i:=match i with 0=>a|1=>b|2=>c|3=>d|4=>e|5=>f|6=>g|_=>h end.
Definition source_reflection_geometry_point M domain level sb sc count a K beta out:=
 exists memberAK ordinals kf union ordinal limit memberAB subsets,
 sf_relation M SFMember a K memberAK /\source_cofinal_ordinals M K ordinals /\source_reflection_KF M domain level sb sc count K kf /\
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union /\numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\
 source_reflection_geometry_instance M ReflectionLimit(fun _=>beta)limit /\sf_relation M SFMember a beta memberAB /\
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets /\
 code_relation M(source_reflection_geometry_values memberAK ordinals kf union ordinal limit memberAB subsets)(source_prop_expression source_reflection_geometry_payload)out.
Theorem source_reflection_geometry_point_total M domain level sb sc count a K beta:
 exists out,source_reflection_geometry_point M domain level sb sc count a K beta out.
Proof.
 destruct(sf_relation_total M SFMember a K)as(mAK&HMAK).
 destruct(source_cofinal_ordinals_total M K)as(ordinals&HO).
 destruct(source_reflection_KF_total M domain level sb sc count K)as(kf&HKF).
 destruct(source_reflection_geometry_instance_total M ReflectionUnion(source_rec_env2 K beta))as(union&HU).
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)beta)as(ordinal&HB).
 destruct(source_reflection_geometry_instance_total M ReflectionLimit(fun _=>beta))as(limit&HL).
 destruct(sf_relation_total M SFMember a beta)as(mAB&HMAB).
 destruct(source_reflection_geometry_instance_total M ReflectionSubsets(source_rec_env2 K beta))as(subsets&HS).
 destruct(code_relation_total M(source_prop_expression source_reflection_geometry_payload)(source_reflection_geometry_values mAK ordinals kf union ordinal limit mAB subsets))as(out&HP).
 exists out,mAK,ordinals,kf,union,ordinal,limit,mAB,subsets. auto 20.
Qed.
Theorem source_reflection_geometry_point_functional M domain level sb sc count a K beta x y:
 source_reflection_geometry_point M domain level sb sc count a K beta x ->source_reflection_geometry_point M domain level sb sc count a K beta y ->x=y.
Proof.
 intros(m&o&kf&u&ob&l&mb&s&HM&HO&HKF&HU&HOB&HL&HMB&HS&HX)
 (m'&o'&kf'&u'&ob'&l'&mb'&s'&HM'&HO'&HKF'&HU'&HOB'&HL'&HMB'&HS'&HY).
 assert(E:m'=m)by(eapply sf_relation_functional;eassumption). subst m'.
 assert(E:o'=o)by(eapply code_relation_functional;eassumption). subst o'.
 assert(E:kf'=kf)by(eapply source_reflection_KF_functional;eassumption). subst kf'.
 assert(E:u'=u)by(eapply code_relation_functional;eassumption). subst u'.
 assert(E:ob'=ob)by(eapply numerical_instantiation_functional;eassumption). subst ob'.
 assert(E:l'=l)by(eapply code_relation_functional;eassumption). subst l'.
 assert(E:mb'=mb)by(eapply sf_relation_functional;eassumption). subst mb'.
 assert(E:s'=s)by(eapply code_relation_functional;eassumption). subst s'.
 exact(code_relation_functional M _ _ x y HX HY).
Qed.
Theorem source_reflection_geometry_point_bounded M domain level sb sc count a K beta out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 coding_lt M a k ->coding_lt M K k ->coding_lt M beta k ->source_reflection_geometry_point M domain level sb sc count a K beta out ->source_bounded M out k.
Proof.
 intros HD HL HV BA BK BB(m&o&kf&u&ob&l&mb&s&HM&HO&HKF&HU&HOB&HLg&HMB&HS&HP).
 pose proof(proj2(source_bounded_accept_atom M SFMember a K m k(or_introl eq_refl)HM)(conj BA BK))as BM.
 pose proof(source_cofinal_ordinals_bounded M K o k BK HO)as BO.
 pose proof(source_reflection_KF_bounded M domain level sb sc count K kf k HD HL HV BK HKF)as BKF.
 assert(BNames:forall i,(i<2)%nat ->coding_lt M(source_rec_env2 K beta i)k)by(intros[|i]HI;[exact BK|exact BB]).
 pose proof(source_reflection_geometry_instance_bounded M ReflectionUnion(source_rec_env2 K beta)u k BNames HU)as BU.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob k(source_ordinal_predicate_bounded M)BB HOB)as BOB.
 pose proof(source_reflection_geometry_instance_bounded M ReflectionLimit(fun _=>beta)l k ltac:(intros i HI;exact BB)HLg)as BL.
 pose proof(proj2(source_bounded_accept_atom M SFMember a beta mb k(or_introl eq_refl)HMB)(conj BA BB))as BMB.
 pose proof(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)s k BNames HS)as BS.
 apply(source_prop_template_bound M(source_reflection_geometry_values m o kf u ob l mb s)source_reflection_geometry_payload k);[|exact HP].
 intros[|[|[|[|[|[|[|i]]]]]]];cbn[source_reflection_geometry_values];assumption.
Qed.
Theorem source_reflection_geometry_payload_program:
 source_prop_program[SPTSlot 0;SPTSlot 1;SPTSlot 2;SPTSlot 3;SPTSlot 4;SPTSlot 5;SPTSlot 6;SPTSlot 7]source_reflection_geometry_payload.
Proof. unfold source_reflection_geometry_payload. repeat apply SPTCI;apply SPTCtx;cbn;tauto. Qed.
Print Assumptions source_reflection_geometry_point_total.
Print Assumptions source_reflection_geometry_point_functional.
Print Assumptions source_reflection_geometry_point_bounded.
Print Assumptions source_reflection_geometry_payload_program.
