(** Actual shifts and witness-zero instantiation of the reflection existence
    shell. The internally quantified matrix is fixed by its proved free bound. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceDomainInstances SourceOrdinalPredicate SourceUnarySubstitution
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenaming RenamingSubstitution SubstitutionSource
 SourceSubstitutionIdentity SourceReflectionGeometryTransport SourceReflectionGeometryPredicates
 SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionExists SourceQuantifierRules SourceRecursionShiftGraphs.
Unset Implicit Arguments.

Theorem source_ordinary_reflection_point_zero_substitution M domain count phi seed old seed' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection_point M domain count phi seed(zeroM M)old ->
 source_ordinary_reflection_point M domain count phi seed'(zeroM M)new ->
 substitution_lookup M rb rc rn base seed seed' ->substitution_lookup M rb rc rn base(zeroM M)(zeroM M) ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HP(o&l&m&r&t&mid&HO&HL&HM&HR&HT&HMid&HOut)
  (o'&l'&m'&r'&t'&mid'&HO'&HL'&HM'&HR'&HT'&HMid'&HOut')HSeed HZero.
 pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)(zeroM M)o rb rc rn base
  (zeroM M)o'(source_ordinal_predicate_bounded M)HO HZero HO')as SO.
 pose proof(source_reflection_geometry_substitution M ReflectionLimit(fun _=>zeroM M)(fun _=>zeroM M)l l' rb rc rn base
  HL HL' ltac:(intros;exact HZero))as SL.
 assert(SM:numerical_substitution M m rb rc rn base m').
 { apply(proj2(numerical_substitution_member M seed(zeroM M)m rb rc rn base m' HM)).
   exists seed',(zeroM M). auto. }
 pose proof(source_ordinary_reflection_functional M domain count phi(zeroM M)r r' HR HR')as E. subst r'.
 pose proof(source_ordinary_reflection_bounded M domain count phi(zeroM M)r(code_numeral M 1)
  HD HP(coding_zero_lt_succ M(zeroM M))HR)as BR.
 assert(SR:numerical_substitution M r rb rc rn base r).
 { apply(numerical_substitution_identity_on_bound M r rb rc rn base(code_numeral M 1)BR).
   intros i HI. rewrite(domain_index_below_one M i HI). exact HZero. }
 assert(ST:numerical_substitution M t rb rc rn base t').
 { apply(proj2(numerical_substitution_binary M SFAnd m r t rb rc rn base t'(or_introl eq_refl)HT)).
   exists m',r. auto. }
 assert(SMid:numerical_substitution M mid rb rc rn base mid').
 { apply(proj2(numerical_substitution_binary M SFAnd l t mid rb rc rn base mid'(or_introl eq_refl)HMid)).
   exists l',t'. auto. }
 apply(proj2(numerical_substitution_binary M SFAnd o mid old rb rc rn base new(or_introl eq_refl)HOut)).
 exists o',mid'. auto.
Qed.

Theorem source_ordinary_reflection_exists_substitution M domain count phi seed old seed' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection_exists M domain count phi seed old ->
 source_ordinary_reflection_exists M domain count phi seed' new ->
 substitution_lookup M rb rc rn base seed seed' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HP(point&HPoint&HEx)(point'&HPoint'&HEx')HSeed.
 destruct(substitution_lift_total M rb rc rn base)as(b&c&n&HLift).
 apply(proj2(numerical_substitution_quantifier M false point old rb rc rn base new HEx)).
 exists b,c,n,point'. split;[exact HLift|]. split;[|exact HEx'].
 exact(source_ordinary_reflection_point_zero_substitution M domain count phi(succM M seed)point(succM M seed')point'
  b c n(succM M base)HD HP HPoint HPoint'
  (proj2(proj2 HLift)seed seed' HSeed)(proj1(proj2 HLift))).
Qed.

Theorem source_ordinary_reflection_exists_shift M domain count phi seed old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection_exists M domain count phi seed old ->
 source_ordinary_reflection_exists M domain count phi(succM M seed)new ->source_formula_shift M old new.
Proof.
 intros HD HP HO HN.
 apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_ordinary_reflection_exists_substitution M domain count phi seed old(succM M seed)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HP HO HN(source_rec_shift_lookup M seed)).
Qed.

Theorem source_ordinary_reflection_exists_instance_zero M domain count phi seed body ex point:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection_point M domain count phi(succM M seed)(zeroM M)body ->
 sf_relation M SFEx body(zeroM M)ex ->
 source_ordinary_reflection_point M domain count phi seed(zeroM M)point ->
 numerical_instantiation M body(zeroM M)point.
Proof.
 intros HD HP HBody HEx HPoint.
 destruct(substitution_singleton_total M(zeroM M))as(b&c&HHead&HTail).
 exists b,c. split;[exact HHead|].
 exact(source_ordinary_reflection_point_zero_substitution M domain count phi(succM M seed)body seed point
  b c(code_numeral M 1)(zeroM M)HD HP HBody HPoint(substitution_singleton_tail M b c seed)HHead).
Qed.

Print Assumptions source_ordinary_reflection_point_zero_substitution.
Print Assumptions source_ordinary_reflection_exists_substitution.
Print Assumptions source_ordinary_reflection_exists_shift.
Print Assumptions source_ordinary_reflection_exists_instance_zero.
