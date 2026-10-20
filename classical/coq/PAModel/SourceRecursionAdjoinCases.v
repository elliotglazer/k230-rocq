(** The actual fixed value-case law at arbitrary internal source names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceLFixed SourceLNonempty
 OldZFRProofLift SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceFiniteParameters SourceFiniteNameParameters
 SourceRecursionPrimitiveRelations SourceRecursionSetOperations SourceRecursionParameterCalibration SourceRecursionAdjoinCasesOld
 SourcePropositionalRebase SchemaConstructorBounds.
From OldZF Require Std_setbase.
Unset Implicit Arguments.
Definition source_rec_adjoin_cases_expression:=source_parameter_expression(source_finite_parameter_names 7)(isolated_formula old_recursion_adjoin_cases_law).
Definition source_rec_env7 {A:Type}(a b c d e f g:A)i:=match i with 0=>a|1=>b|2=>c|3=>d|4=>e|5=>f|_=>g end.
Theorem source_zfr_rec_adjoin_cases_named M rho out:code_relation M rho source_rec_adjoin_cases_expression out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 refine(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(isolated_formula old_recursion_adjoin_cases_law)7 rho out _ HG).
 apply(proj2(source_zfr_descriptor_provable M _)). exact(finite_old_zfr_proof_lift M old_L_background old_recursion_adjoin_cases_law old_L_background_valid old_recursion_adjoin_cases_proof).
Qed.
Theorem source_rec_adjoin_cases_shell M f q g z w u v law:
 code_relation M(source_rec_env7 f q g z w u v)source_rec_adjoin_cases_expression law ->
 exists adj op app old equalU equalV both cases t2 t1,
 source_rec_adjoin M f q g adj /\source_rec_ordered_pair M z w q op /\source_rec_app M g u v app /\source_rec_app M f u v old /\
 sf_relation M SFEqual u z equalU /\sf_relation M SFEqual v w equalV /\sf_relation M SFAnd equalU equalV both /\sf_relation M SFOr old both cases /\
 sf_relation M SFImpl app cases t2 /\sf_relation M SFImpl op t2 t1 /\sf_relation M SFImpl adj t1 law.
Proof.
 intro HG. set(rho:=source_rec_env7 f q g z w u v). set(names:=source_finite_parameter_names 7).
 set(ADJ:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)))).
 set(OP:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 1)))).
 set(APP:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 6)))).
 set(OLD:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 6)))).
 set(EU:=E_sf SFEqual(names 5)(names 3)). set(EV:=E_sf SFEqual(names 6)(names 4)). set(BOTH:=E_sf SFAnd EU EV). set(CASES:=E_sf SFOr OLD BOTH).
 change(code_relation M rho(E_sf SFImpl ADJ(E_sf SFImpl OP(E_sf SFImpl APP CASES)))law)in HG.
 destruct(schema_expression_split M rho SFImpl _ _ law HG)as(adj&t1&HA&HT1&H1).
 destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(op&t2&HO&HT2&H2).
 destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(app&cases&HApp&HCases&H3).
 destruct(schema_expression_split M rho SFOr OLD BOTH cases HCases)as(old&both&HOld&HBoth&HOr).
 destruct(schema_expression_split M rho SFAnd EU EV both HBoth)as(eu&ev&HEU&HEV&HAnd).
 pose proof(source_parameter_rec_adjoin M names rho 0 1 2 f q g adj eq_refl eq_refl eq_refl HA)as HAdj.
 pose proof(source_parameter_rec_ordered_pair M names rho 3 4 1 z w q op eq_refl eq_refl eq_refl HO)as HOp.
 pose proof(source_parameter_rec_app M names rho 2 5 6 g u v app eq_refl eq_refl eq_refl HApp)as HAppG.
 pose proof(source_parameter_rec_app M names rho 0 5 6 f u v old eq_refl eq_refl eq_refl HOld)as HAppF.
 pose proof(proj1(schema_expression_graph M rho SFEqual(names 5)(names 3)u z eu eq_refl eq_refl)HEU)as HEqualU.
 pose proof(proj1(schema_expression_graph M rho SFEqual(names 6)(names 4)v w ev eq_refl eq_refl)HEV)as HEqualV.
 exists adj,op,app,old,eu,ev,both,cases,t2,t1. auto 12.
Qed.
Theorem source_zfr_rec_adjoin_cases_total M f q g z w u v:
 exists adj op app old equalU equalV both cases t2 t1 law,
 source_rec_adjoin M f q g adj /\source_rec_ordered_pair M z w q op /\source_rec_app M g u v app /\source_rec_app M f u v old /\
 sf_relation M SFEqual u z equalU /\sf_relation M SFEqual v w equalV /\sf_relation M SFAnd equalU equalV both /\sf_relation M SFOr old both cases /\
 sf_relation M SFImpl app cases t2 /\sf_relation M SFImpl op t2 t1 /\sf_relation M SFImpl adj t1 law /\source_zfr_provable M law.
Proof.
 destruct(code_relation_total M source_rec_adjoin_cases_expression(source_rec_env7 f q g z w u v))as(law&HG).
 destruct(source_rec_adjoin_cases_shell M f q g z w u v law HG)as(adj&op&app&old&eu&ev&both&cases&t2&t1&HA&HO&HApp&HOld&HEU&HEV&HB&HC&H3&H2&H1).
 exists adj,op,app,old,eu,ev,both,cases,t2,t1,law. split;[exact HA|]. split;[exact HO|]. split;[exact HApp|]. split;[exact HOld|].
 split;[exact HEU|]. split;[exact HEV|]. split;[exact HB|]. split;[exact HC|]. split;[exact H3|]. split;[exact H2|]. split;[exact H1|].
 exact(source_zfr_rec_adjoin_cases_named M(source_rec_env7 f q g z w u v)law HG).
Qed.
Print Assumptions source_zfr_rec_adjoin_cases_named.
Print Assumptions source_rec_adjoin_cases_shell.
Print Assumptions source_zfr_rec_adjoin_cases_total.
