(** Literal calibration of the fixed initial-value clause. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters
 SourceRecursionParameterCalibration SourceRecursionAttempt SourceRecursionZeroExtensionOld SourcePropositionalRebase SchemaConstructorBounds.
From OldZF Require Std_setbase.
Unset Implicit Arguments.
Theorem source_parameter_rec_zero_clause M names rho i j l o a f out:
 code_relation M rho(names i)o ->code_relation M rho(names j)a ->code_relation M rho(names l)f ->
 code_relation M rho(source_parameter_expression names(isolated_formula(old_recursion_zero_clause
  (@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j)(@OC.var OB.sig_empty l))))out ->source_rec_attempt_zero M o a f out.
Proof.
 intros HI HJ HL HG. set(up:=source_parameter_up names).
 set(APP:=source_parameter_expression up(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty(S l))(@OC.var OB.sig_empty(S i))(@OC.var OB.sig_empty 0)))).
 set(EQ:=E_sf SFEqual(up 0)(up(S j))).
 change(code_relation M rho(E_sf SFAll(E_sf SFImpl APP EQ)(CEconst 0))out)in HG.
 destruct(schema_expression_split M rho SFAll _ _ out HG)as(point&z0&HPoint&HZ&HAll). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFImpl APP EQ point HPoint)as(app&equal&HApp&HEqual&HImpl).
 assert(U0:code_relation M rho(up 0)(zeroM M))by reflexivity.
 pose proof(source_parameter_up_name M names rho i o HI)as UI.
 pose proof(source_parameter_up_name M names rho j a HJ)as UJ.
 pose proof(source_parameter_up_name M names rho l f HL)as UL.
 pose proof(source_parameter_rec_app M up rho(S l)(S i)0 _ _ _ app UL UI U0 HApp)as HAppGraph.
 pose proof(proj1(schema_expression_graph M rho SFEqual(up 0)(up(S j))(zeroM M)(succM M a)equal U0 UJ)HEqual)as HEqualGraph.
 exists app,equal,point. auto.
Qed.
Print Assumptions source_parameter_rec_zero_clause.
