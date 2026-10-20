(** Actual AllE and both proof directions of the ordinal subcarrier chart. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
 NumericalInstantiation NumericalContexts NumericalSourceFull SourceConjunctionRules SourceNamedProofRules SourceDerivedRules SourceQuantifierRules SourceTraceBounds SourceInstantiationConstructors
 SourceOrdinalPredicate SourceReflectionOrdinalChart SourcePropositionalTemplates SourceSeparationSubset SourceWFSeparationWitness SourceTracePointRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_full_reflection_ordinal_chart_point M b c n Y K chart z left right ordinal point:
 source_reflection_ordinal_chart M Y K chart ->sf_relation M SFMember z K left ->sf_relation M SFMember z Y right ->
 numerical_instantiation M(source_ordinal_predicate_code M)z ordinal ->
 code_relation M(schema_env3 left right ordinal)(source_prop_expression separation_point_template)point ->
 source_full_prv M b c n chart ->source_full_prv M b c n point.
Proof.
 intros(l&r&p&HL&HR&HP&HA)HLeft HRight HOrd HPoint PChart.
 assert(HInst:numerical_instantiation M p z point).
 { apply(source_prop_expression_instantiation M(schema_env3 l r(source_ordinal_predicate_code M))(schema_env3 left right ordinal)z separation_point_template p point);[|exact HP|exact HPoint].
   intros[|[|i]];cbn[schema_env3].
   - exact(source_instantiation_head_member M K l z left HL HLeft).
   - exact(source_instantiation_head_member M Y r z right HR HRight).
   - exact HOrd. }
 exact(full_source_AllE M b c n p chart z point(source_wf_quantifier_instance M b c n SFAll p chart z point(or_introl eq_refl)HA(source_full_prv_wellformed M b c n chart PChart)HInst)PChart HA HInst).
Qed.
Theorem source_full_reflection_ordinal_chart_out M b c n Y K chart z left right ordinal:
 source_reflection_ordinal_chart M Y K chart ->sf_relation M SFMember z K left ->sf_relation M SFMember z Y right ->
 numerical_instantiation M(source_ordinal_predicate_code M)z ordinal ->
 source_full_prv M b c n chart ->source_full_prv M b c n left ->
 source_full_prv M b c n right /\source_full_prv M b c n ordinal.
Proof.
 intros HC HL HR HO PC PL.
 destruct(code_relation_total M(source_prop_expression separation_point_template)(schema_env3 left right ordinal))as(point&HP).
 pose proof(source_full_reflection_ordinal_chart_point M b c n Y K chart z left right ordinal point HC HL HR HO HP PC)as PP.
 destruct(source_trace_point_unpack M left right ordinal point HP)as(rhs&forward&backward&HAnd&HF&HB&HI).
 pose proof(source_full_conjunction_left M b c n forward backward point HI PP)as PF.
 pose proof(source_full_modus_ponens M b c n left rhs forward HF PF PL)as PRhs.
 split;[exact(source_full_conjunction_left M b c n right ordinal rhs HAnd PRhs)|exact(source_full_conjunction_right M b c n right ordinal rhs HAnd PRhs)].
Qed.
Theorem source_full_reflection_ordinal_chart_in M b c n Y K chart z left right ordinal:
 source_reflection_ordinal_chart M Y K chart ->sf_relation M SFMember z K left ->sf_relation M SFMember z Y right ->
 numerical_instantiation M(source_ordinal_predicate_code M)z ordinal ->
 source_full_prv M b c n chart ->source_full_prv M b c n right ->source_full_prv M b c n ordinal ->source_full_prv M b c n left.
Proof.
 intros HC HL HR HO PC PR PO.
 destruct(code_relation_total M(source_prop_expression separation_point_template)(schema_env3 left right ordinal))as(point&HP).
 pose proof(source_full_reflection_ordinal_chart_point M b c n Y K chart z left right ordinal point HC HL HR HO HP PC)as PP.
 destruct(source_trace_point_unpack M left right ordinal point HP)as(rhs&forward&backward&HAnd&HF&HB&HI).
 pose proof(source_full_conjunction_right M b c n forward backward point HI PP)as PB.
 exact(source_full_modus_ponens M b c n rhs left backward HB PB(source_full_and_intro M b c n right ordinal rhs HAnd PR PO)).
Qed.
Print Assumptions source_full_reflection_ordinal_chart_point.
Print Assumptions source_full_reflection_ordinal_chart_out.
Print Assumptions source_full_reflection_ordinal_chart_in.
