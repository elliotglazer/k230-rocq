(** Open the actual reflected ordinal at an arbitrary name, keeping the bound matrix closed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceDomainInstances SourceOrdinalPredicate SourceUnarySubstitution
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
 SourceReflectionGeometryTransport SourceReflectionGeometryPredicates SourceOrdinaryReflectionSyntax
 SourceOrdinaryReflectionTransport SourceOrdinaryReflectionExists SourceFreshQuantifierProofs
 NumericalContexts NumericalSourceFull.
Unset Implicit Arguments.
Theorem source_ordinary_reflection_point_substitution M domain count phi seed beta old seed' beta' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection_point M domain count phi seed beta old ->
 source_ordinary_reflection_point M domain count phi seed' beta' new ->
 substitution_lookup M rb rc rn base seed seed' ->substitution_lookup M rb rc rn base beta beta' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HP(o&l&m&r&t&mid&HO&HL&HM&HR&HT&HMid&HOut)
  (o'&l'&m'&r'&t'&mid'&HO'&HL'&HM'&HR'&HT'&HMid'&HOut')HSeed HBeta.
 pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)beta o rb rc rn base
  beta' o'(source_ordinal_predicate_bounded M)HO HBeta HO')as SO.
 pose proof(source_reflection_geometry_substitution M ReflectionLimit(fun _=>beta)(fun _=>beta')l l' rb rc rn base
  HL HL' ltac:(intros;exact HBeta))as SL.
 assert(SM:numerical_substitution M m rb rc rn base m').
 { apply(proj2(numerical_substitution_member M seed beta m rb rc rn base m' HM)). exists seed',beta'. auto. }
 pose proof(source_ordinary_reflection_substitution M domain count phi beta r beta' r' rb rc rn base HD HP HR HR' HBeta)as SR.
 assert(ST:numerical_substitution M t rb rc rn base t').
 { apply(proj2(numerical_substitution_binary M SFAnd m r t rb rc rn base t'(or_introl eq_refl)HT)). exists m',r'. auto. }
 assert(SMid:numerical_substitution M mid rb rc rn base mid').
 { apply(proj2(numerical_substitution_binary M SFAnd l t mid rb rc rn base mid'(or_introl eq_refl)HMid)). exists l',t'. auto. }
 apply(proj2(numerical_substitution_binary M SFAnd o mid old rb rc rn base new(or_introl eq_refl)HOut)).
 exists o',mid'. auto.
Qed.
Theorem source_ordinary_reflection_witness_instantiation M domain count phi seed beta body point:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection_point M domain count phi(succM M seed)(zeroM M)body ->
 source_ordinary_reflection_point M domain count phi seed beta point ->
 numerical_instantiation M body beta point.
Proof.
 intros HD HP HBody HPoint. destruct(substitution_singleton_total M beta)as(b&c&HHead&HTail).
 exists b,c. split;[exact HHead|].
 exact(source_ordinary_reflection_point_substitution M domain count phi(succM M seed)(zeroM M)body seed beta point
  b c(code_numeral M 1)(zeroM M)HD HP HBody HPoint(HTail seed)HHead).
Qed.
Theorem source_full_ordinary_reflection_fresh_elim M domain count phi seed beta whole point goal imp gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->coding_lt M seed k ->
 context_bounded M gb gc gn k ->source_bounded M goal k ->coding_lt M k(succM M beta) ->
 source_ordinary_reflection_exists M domain count phi seed whole ->
 source_ordinary_reflection_point M domain count phi seed beta point ->sf_relation M SFImpl point goal imp ->
 source_full_prv M gb gc gn imp ->source_full_prv M gb gc gn whole ->source_full_prv M gb gc gn goal.
Proof.
 intros HD HP BS HC BG HF HWhole HPoint HImp PImp PWhole.
 destruct HWhole as(body&HBody&HEx).
 assert(BWhole:source_bounded M whole k).
 { exact(source_ordinary_reflection_exists_bounded M domain count phi seed whole k HD HP BS(ex_intro _ body(conj HBody HEx))). }
 pose proof(proj1(source_bounded_accept_unary M SFEx body whole k(or_intror eq_refl)HEx)BWhole)as BBody.
 exact(source_full_fresh_exists_elim M gb gc gn body whole beta point goal imp k HC BBody BG HF HEx
  (source_ordinary_reflection_witness_instantiation M domain count phi seed beta body point HD HP HBody HPoint)HImp PImp PWhole).
Qed.
Print Assumptions source_ordinary_reflection_point_substitution.
Print Assumptions source_ordinary_reflection_witness_instantiation.
Print Assumptions source_full_ordinary_reflection_fresh_elim.
