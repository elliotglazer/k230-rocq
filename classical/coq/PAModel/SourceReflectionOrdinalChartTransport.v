(** Actual substitution/shift of the ordinal-subcarrier chart. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceSubstitutionIdentity SourceDomainInstances SourceOrdinalPredicate SourcePropositionalSubstitution SourcePropositionalTemplates SourceSeparationSubset
 SourceReflectionOrdinalChart SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_reflection_ordinal_chart_substitution M Y K old Y' K' new rb rc rn base:
 source_reflection_ordinal_chart M Y K old ->source_reflection_ordinal_chart M Y' K' new ->
 substitution_lookup M rb rc rn base Y Y' ->substitution_lookup M rb rc rn base K K' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros(l&r&p&HL&HR&HP&HA)(l'&r'&p'&HL'&HR'&HP'&HA')HY HK.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HMap).
 assert(SL:numerical_substitution M l lb lc ln(succM M base)l').
 { apply(proj2(numerical_substitution_member M(zeroM M)(succM M K)l lb lc ln(succM M base)l' HL)).
   exists(zeroM M),(succM M K'). split;[exact(proj1(proj2 HMap))|]. split;[exact(proj2(proj2 HMap)K K' HK)|exact HL']. }
 assert(SR:numerical_substitution M r lb lc ln(succM M base)r').
 { apply(proj2(numerical_substitution_member M(zeroM M)(succM M Y)r lb lc ln(succM M base)r' HR)).
   exists(zeroM M),(succM M Y'). split;[exact(proj1(proj2 HMap))|]. split;[exact(proj2(proj2 HMap)Y Y' HY)|exact HR']. }
 assert(SO:numerical_substitution M(source_ordinal_predicate_code M)lb lc ln(succM M base)(source_ordinal_predicate_code M)).
 { apply(numerical_substitution_identity_on_bound M _ lb lc ln(succM M base)(code_numeral M 1)(source_ordinal_predicate_bounded M)).
   intros i HI. rewrite(domain_index_below_one M i HI). exact(proj1(proj2 HMap)). }
 assert(SP:numerical_substitution M p lb lc ln(succM M base)p').
 { apply(source_prop_expression_substitution M(schema_env3 l r(source_ordinal_predicate_code M))(schema_env3 l' r'(source_ordinal_predicate_code M))lb lc ln(succM M base)separation_point_template);[|exact HP|exact HP'].
   intros[|[|i]];cbn[schema_env3];assumption. }
 apply(proj2(numerical_substitution_quantifier M true p old rb rc rn base new HA)).
 exists lb,lc,ln,p'. auto.
Qed.
Theorem source_reflection_ordinal_chart_shift M Y K old new:
 source_reflection_ordinal_chart M Y K old ->source_reflection_ordinal_chart M(succM M Y)(succM M K)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_reflection_ordinal_chart_substitution M Y K old(succM M Y)(succM M K)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M Y)(source_rec_shift_lookup M K)).
Qed.
Print Assumptions source_reflection_ordinal_chart_substitution.
Print Assumptions source_reflection_ordinal_chart_shift.
