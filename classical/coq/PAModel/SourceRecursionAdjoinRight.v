(** The actual fixed App-adjoin-right law in the shared primitive graphs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters
 SourceRecursionFactsOld SourceRecursionFacts SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionParameterCalibration
 SourceRecursionSetOperations SourcePropositionalRebase SchemaConstructorBounds SourceZFRProvability.
From OldZF Require Std_setbase.
Unset Implicit Arguments.
Theorem source_rec_adjoin_right_shell M f q g u v law:
 source_recursion_fact_graph M RecAppAdjRight(source_rec_env5 f q g u v)law ->exists adj old new point,
 source_rec_adjoin M f q g adj /\source_rec_ordered_pair M u v q old /\source_rec_app M g u v new /\
 sf_relation M SFImpl old new point /\sf_relation M SFImpl adj point law.
Proof.
 intro HG. set(rho:=source_rec_env5 f q g u v). set(names:=source_finite_parameter_names 6).
 set(ADJ:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)))).
 set(OLD:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 1)))).
 set(NEW:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)))).
 change(code_relation M rho(E_sf SFImpl ADJ(E_sf SFImpl OLD NEW))law)in HG.
 destruct(schema_expression_split M rho SFImpl ADJ(E_sf SFImpl OLD NEW)law HG)as(adj&point&HAdj&HPoint&HL).
 destruct(schema_expression_split M rho SFImpl OLD NEW point HPoint)as(old&new&HO&HN&HP).
 exists adj,old,new,point. split;[exact(source_parameter_rec_adjoin M names rho 0 1 2 f q g adj eq_refl eq_refl eq_refl HAdj)|].
 split;[exact(source_parameter_rec_ordered_pair M names rho 3 4 1 u v q old eq_refl eq_refl eq_refl HO)|].
 split;[exact(source_parameter_rec_app M names rho 2 3 4 g u v new eq_refl eq_refl eq_refl HN)|]. auto.
Qed.
Theorem source_zfr_rec_adjoin_right M f q g u v adj old new point law:
 source_rec_adjoin M f q g adj ->source_rec_ordered_pair M u v q old ->source_rec_app M g u v new ->
 sf_relation M SFImpl old new point ->sf_relation M SFImpl adj point law ->source_zfr_provable M law.
Proof.
 intros HA HO HN HP HL.
 destruct(source_zfr_recursion_fact_total M RecAppAdjRight(source_rec_env5 f q g u v))as(law'&HG&PG).
 destruct(source_rec_adjoin_right_shell M f q g u v law' HG)as(adj'&old'&new'&point'&HA'&HO'&HN'&HP'&HL').
 pose proof(code_relation_functional M _ _ adj' adj HA' HA)as E. subst adj'.
 pose proof(code_relation_functional M _ _ old' old HO' HO)as E. subst old'.
 pose proof(code_relation_functional M _ _ new' new HN' HN)as E. subst new'.
 pose proof(sf_relation_functional M SFImpl old new point' point HP' HP)as E. subst point'.
 pose proof(sf_relation_functional M SFImpl adj point law' law HL' HL)as E. now subst law'.
Qed.
Print Assumptions source_rec_adjoin_right_shell.
Print Assumptions source_zfr_rec_adjoin_right.
