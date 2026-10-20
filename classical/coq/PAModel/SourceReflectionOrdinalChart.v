(** The exact ordinal subcarrier chart: forall z,z in K iff z in Y and Ord(z). *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundMonotone
 SourceOrdinalPredicate SourcePropositionalTemplates SourceSeparationSubset SourceWFSeparationWitness SourceTracePointRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Definition source_reflection_ordinal_chart M Y K out:=exists left right point,
 sf_relation M SFMember(zeroM M)(succM M K)left /\sf_relation M SFMember(zeroM M)(succM M Y)right /\
 code_relation M(schema_env3 left right(source_ordinal_predicate_code M))(source_prop_expression separation_point_template)point /\
 sf_relation M SFAll point(zeroM M)out.
Theorem source_reflection_ordinal_chart_total M Y K:exists out,source_reflection_ordinal_chart M Y K out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M K))as(left&HL).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M Y))as(right&HR).
 destruct(code_relation_total M(source_prop_expression separation_point_template)(schema_env3 left right(source_ordinal_predicate_code M)))as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO).
 exists out,left,right,point. auto.
Qed.
Theorem source_reflection_ordinal_chart_functional M Y K a b:
 source_reflection_ordinal_chart M Y K a ->source_reflection_ordinal_chart M Y K b ->a=b.
Proof.
 intros(l&r&p&HL&HR&HP&HA)(l'&r'&p'&HL'&HR'&HP'&HB).
 assert(E:l'=l)by(eapply sf_relation_functional;eassumption). subst l'.
 assert(E:r'=r)by(eapply sf_relation_functional;eassumption). subst r'.
 assert(E:p'=p)by(eapply code_relation_functional;eassumption). subst p'.
 exact(sf_relation_functional M SFAll p(zeroM M)a b HA HB).
Qed.
Theorem source_reflection_ordinal_chart_bounded M Y K out k:
 coding_lt M Y k ->coding_lt M K k ->source_reflection_ordinal_chart M Y K out ->source_bounded M out k.
Proof.
 intros BY BK(l&r&p&HL&HR&HP&HA).
 assert(BL:source_bounded M l(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ l _ (or_introl eq_refl)HL)). split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M K k)BK)]. }
 assert(BR:source_bounded M r(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ r _ (or_introl eq_refl)HR)). split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M Y k)BY)]. }
 assert(BO:source_bounded M(source_ordinal_predicate_code M)(succM M k)).
 { exact(source_bounded_monotone M _ (code_numeral M 1)(succM M k)(source_ordinal_predicate_bounded M)
   (proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))(coding_zero_lt_succ M k))). }
 apply(proj2(source_bounded_accept_unary M SFAll p out k(or_introl eq_refl)HA)).
 apply(source_prop_template_bound M(schema_env3 l r(source_ordinal_predicate_code M))separation_point_template(succM M k));[|exact HP].
 intros[|[|i]];cbn[schema_env3];assumption.
Qed.
Print Assumptions source_reflection_ordinal_chart_total.
Print Assumptions source_reflection_ordinal_chart_functional.
Print Assumptions source_reflection_ordinal_chart_bounded.
