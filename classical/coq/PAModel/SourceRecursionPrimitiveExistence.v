(** Actual ordered-pair and adjoining-set existence in the common graphs. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters
 SourceRecursionFactsOld SourceRecursionFacts SourceRecursionPrimitiveRelations SourceRecursionSetOperations SourceZFRProvability.
From OldZF Require Std_setbase.
Unset Implicit Arguments.

Theorem source_zfr_rec_ordered_pair_exists M x y:exists body out,
 source_rec_ordered_pair M(succM M x)(succM M y)(zeroM M)body /\
 sf_relation M SFEx body(zeroM M)out /\source_zfr_provable M out.
Proof.
 destruct(source_zfr_recursion_fact_total M RecOpExists(source_rec_env2 x y))as(out&HG&PG).
 set(rho:=source_rec_env2 x y). set(names:=source_finite_parameter_names 6).
 set(BODY:=source_parameter_expression(source_parameter_up names)
  (isolated_formula(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 0)))).
 change(code_relation M rho(E_sf SFEx BODY(CEconst 0))out)in HG.
 destruct(code_relation_total M BODY rho)as(body&HB).
 pose proof(proj1(schema_expression_graph M rho SFEx BODY(CEconst 0)body(zeroM M)out HB eq_refl)HG)as HE.
 assert(HX:code_relation M rho(source_parameter_up names 1)(succM M x)).
 { exists x,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
 assert(HY:code_relation M rho(source_parameter_up names 2)(succM M y)).
 { exists y,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
 exists body,out. split;[|exact(conj HE PG)].
 exact(source_parameter_rec_ordered_pair M(source_parameter_up names)rho 1 2 0
  (succM M x)(succM M y)(zeroM M)body HX HY eq_refl HB).
Qed.

Theorem source_zfr_rec_adjoin_exists M f q:exists body out,
 source_rec_adjoin M(succM M f)(succM M q)(zeroM M)body /\
 sf_relation M SFEx body(zeroM M)out /\source_zfr_provable M out.
Proof.
 destruct(source_zfr_recursion_fact_total M RecAdjExists(source_rec_env2 f q))as(out&HG&PG).
 set(rho:=source_rec_env2 f q). set(names:=source_finite_parameter_names 6).
 set(BODY:=source_parameter_expression(source_parameter_up names)
  (isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 0)))).
 change(code_relation M rho(E_sf SFEx BODY(CEconst 0))out)in HG.
 destruct(code_relation_total M BODY rho)as(body&HB).
 pose proof(proj1(schema_expression_graph M rho SFEx BODY(CEconst 0)body(zeroM M)out HB eq_refl)HG)as HE.
 assert(HF:code_relation M rho(source_parameter_up names 1)(succM M f)).
 { exists f,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
 assert(HQ:code_relation M rho(source_parameter_up names 2)(succM M q)).
 { exists q,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
 exists body,out. split;[|exact(conj HE PG)].
 exact(source_parameter_rec_adjoin M(source_parameter_up names)rho 1 2 0
  (succM M f)(succM M q)(zeroM M)body HF HQ eq_refl HB).
Qed.
Print Assumptions source_zfr_rec_ordered_pair_exists.
Print Assumptions source_zfr_rec_adjoin_exists.
