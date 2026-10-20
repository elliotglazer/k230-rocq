(** Literal shared-graph shell of the actual fixed zero-clause extension proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters
 SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionParameterCalibration SourceRecursionSuccessorCalibration SourceRecursionSetOperations
 SourceRecursionAttempt SourceRecursionZeroExtensionOld SourceRecursionZeroExtensionFixed SourceRecursionZeroClauseCalibration SourceRecursionFreshPredecessorShell
 SourceFiniteTelescope SourcePropositionalRebase SchemaConstructorBounds SourceZFRProvability.
From OldZF Require Std_setbase Std_setrec Std_setinf.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_rec_zero_extension_shell M o a N f z next w q g law:
 code_relation M(source_rec_env9 o a N f z next w q g)source_rec_zero_extension_expression law ->
 exists nonzero member successor adj op old new,
 source_rec_nonzero M o N nonzero /\sf_relation M SFMember z N member /\source_rec_successor M z next successor /\source_rec_adjoin M f q g adj /\
 source_rec_ordered_pair M next w q op /\source_rec_attempt_zero M o a f old /\source_rec_attempt_zero M o a g new /\
 source_finite_telescope M[nonzero;member;successor;adj;op;old]new law.
Proof.
 intro HG. set(rho:=source_rec_env9 o a N f z next w q g). set(names:=source_finite_parameter_names 9).
 set(NZ:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.SNz OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)))).
 set(MEMBER:=E_sf SFMember(names 4)(names 2)).
 set(SUCC:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5)))).
 set(ADJ:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 7)(@OC.var OB.sig_empty 8)))).
 set(OP:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 6)(@OC.var OB.sig_empty 7)))).
 set(OLD:=source_parameter_expression names(isolated_formula(old_recursion_zero_clause(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 3)))).
 set(NEW:=source_parameter_expression names(isolated_formula(old_recursion_zero_clause(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 8)))).
 change(code_relation M rho(E_sf SFImpl NZ(E_sf SFImpl MEMBER(E_sf SFImpl SUCC(E_sf SFImpl ADJ(E_sf SFImpl OP(E_sf SFImpl OLD NEW))))))law)in HG.
 destruct(schema_expression_split M rho SFImpl _ _ law HG)as(nonzero&t1&HNZ&HT1&H1).
 destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(member&t2&HM&HT2&H2).
 destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(successor&t3&HS&HT3&H3).
 destruct(schema_expression_split M rho SFImpl _ _ t3 HT3)as(adj&t4&HA&HT4&H4).
 destruct(schema_expression_split M rho SFImpl _ _ t4 HT4)as(op&t5&HO&HT5&H5).
 destruct(schema_expression_split M rho SFImpl _ _ t5 HT5)as(old&new&HF&HG'&H6).
 exists nonzero,member,successor,adj,op,old,new.
 split;[exact(source_parameter_rec_nonzero M names rho 0 2 o N nonzero eq_refl eq_refl HNZ)|].
 split;[exact(proj1(schema_expression_graph M rho SFMember(names 4)(names 2)z N member eq_refl eq_refl)HM)|].
 split;[exact(source_parameter_rec_rel2_successor M names rho 4 5 z next successor eq_refl eq_refl HS)|].
 split;[exact(source_parameter_rec_adjoin M names rho 3 7 8 f q g adj eq_refl eq_refl eq_refl HA)|].
 split;[exact(source_parameter_rec_ordered_pair M names rho 5 6 7 next w q op eq_refl eq_refl eq_refl HO)|].
 split;[exact(source_parameter_rec_zero_clause M names rho 0 1 3 o a f old eq_refl eq_refl eq_refl HF)|].
 split;[exact(source_parameter_rec_zero_clause M names rho 0 1 8 o a g new eq_refl eq_refl eq_refl HG')|].
 rec_pack_telescope.
Qed.
Theorem source_zfr_rec_zero_extension_total M o a N f z next w q g:
 exists nonzero member successor adj op old new law,
 source_rec_nonzero M o N nonzero /\sf_relation M SFMember z N member /\source_rec_successor M z next successor /\source_rec_adjoin M f q g adj /\
 source_rec_ordered_pair M next w q op /\source_rec_attempt_zero M o a f old /\source_rec_attempt_zero M o a g new /\
 source_finite_telescope M[nonzero;member;successor;adj;op;old]new law /\source_zfr_provable M law.
Proof.
 destruct(code_relation_total M source_rec_zero_extension_expression(source_rec_env9 o a N f z next w q g))as(law&HG).
 destruct(source_rec_zero_extension_shell M o a N f z next w q g law HG)as(nz&member&successor&adj&op&old&new&HNZ&HM&HS&HA&HO&HF&HG'&HT).
 exists nz,member,successor,adj,op,old,new,law. split;[exact HNZ|]. split;[exact HM|]. split;[exact HS|]. split;[exact HA|].
 split;[exact HO|]. split;[exact HF|]. split;[exact HG'|]. split;[exact HT|].
 exact(source_zfr_rec_zero_extension_named M(source_rec_env9 o a N f z next w q g)law HG).
Qed.
Print Assumptions source_rec_zero_extension_shell.
Print Assumptions source_zfr_rec_zero_extension_total.
