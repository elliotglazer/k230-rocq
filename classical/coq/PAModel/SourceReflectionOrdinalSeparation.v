(** Actual ordinal subcarrier existence, using the proved uniform Separation generator. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded
 SourceFiniteCutoffShift SourceSubstitutionIdentity SourceDomainInstances SourceOrdinalPredicate
 SourceZFRSeparationContainer SourceSeparationContainerSpecialization SourceWFSeparationConstructor
 SourceReflectionOrdinalChart SourcePropositionalTemplates SourceSeparationSubset SourceWFSeparationWitness
 SourceNumeralLift SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Lemma source_ordinal_cutoff_one_self M:
 source_cutoff_shift M 1(source_ordinal_predicate_code M)(source_ordinal_predicate_code M).
Proof.
 destruct(source_cutoff_shift_map_total M 1)as(b&c&n&HM). exists b,c,n. split;[exact HM|].
 apply(numerical_substitution_identity_on_bound M _ b c n(code_numeral M 2)(code_numeral M 1)(source_ordinal_predicate_bounded M)).
 intros i HI. rewrite(domain_index_below_one M i HI).
 exact(source_cutoff_shift_map_fixed_lookup M 1 b c n HM 0).
Qed.
Theorem source_zfr_reflection_ordinal_separation M Y:
 exists chart out,source_reflection_ordinal_chart M(succM M Y)(zeroM M)chart /\
 sf_relation M SFEx chart(zeroM M)out /\source_zfr_provable M out.
Proof.
 destruct(source_zfr_separation_container_total M(source_ordinal_predicate_code M)(zeroM M)(source_ordinal_predicate_code M)Y
  (source_ordinal_predicate_bounded M)(source_ordinal_cutoff_one_self M))as(out&HGraph&POut).
 unfold E_separation_container,E_sf_ex,E_sf_all in HGraph.
 destruct(schema_expression_quantifier_split M _ SFEx _ out HGraph)as(chart&HChart&HEx).
 destruct(schema_expression_quantifier_split M _ SFAll _ chart HChart)as(point&HPoint&HAll).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M Y)))as(right&HRight).
 pose proof(proj1(source_sep_container_point_graph M Y(source_ordinal_predicate_code M)right point HRight)HPoint)as HP.
 exists chart,out. split.
 - exists(source_sep_left_code M),right,point. split;[exact(sf_make_numeral M SFMember 0 1)|]. auto.
 - auto.
Qed.
Print Assumptions source_ordinal_cutoff_one_self.
Print Assumptions source_zfr_reflection_ordinal_separation.
