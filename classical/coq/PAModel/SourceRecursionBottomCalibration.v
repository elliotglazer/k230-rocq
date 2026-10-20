(** Literal fixed false-relation attempts compile to the shared numerical attempt graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteCutoffShift
 SourceFiniteParameters SourceFiniteNameParameters SourceRecursionPrimitiveRelations SourceRecursionParameterCalibration SourceRecursionSuccessorCalibration
 SourceRecursionAttempt SourcePropositionalRebase SchemaConstructorBounds SetSchemaConstructors SourceFunctionalityShells.
From OldZF Require Std_setrec Std_setbase Std_setinf.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Fixpoint source_rec_parameter_lift(names:nat->code_expr)(depth:nat):nat->code_expr:=match depth with
 |0=>names|S n=>source_parameter_up(source_rec_parameter_lift names n)end.
Theorem source_rec_parameter_lift_name M names rho depth i v:
 code_relation M rho(names i)v ->code_relation M rho(source_rec_parameter_lift names depth(depth+i))(source_succ_iter M depth v).
Proof.
 intro H. induction depth as[|depth IH];[exact H|]. cbn[source_rec_parameter_lift source_succ_iter Nat.add]. apply source_parameter_up_name. exact IH.
Qed.
Theorem source_rec_parameter_lift_fresh M names rho depth i:(i<depth)%nat ->
 code_relation M rho(source_rec_parameter_lift names depth i)(code_numeral M i).
Proof.
 revert i. induction depth as[|depth IH];intros[|i]HI;try lia.
 - reflexivity.
 - cbn[source_rec_parameter_lift]. change(code_relation M rho(source_parameter_up(source_rec_parameter_lift names depth)(S i))(succM M(code_numeral M i))).
   apply source_parameter_up_name,IH. lia.
Qed.
Theorem source_parameter_rec_bottom_attempt M names rho i j k l o a N f out:
 code_relation M rho(names i)o ->code_relation M rho(names j)a ->code_relation M rho(names k)N ->code_relation M rho(names l)f ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Att OldZF.Std_setinf.phSig (@OC.falsity OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators)
  (@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j)(@OC.var OB.sig_empty k)(@OC.var OB.sig_empty l))))out ->
 source_rec_attempt M(zeroM M)o a N f out.
Proof.
 intros HI HJ HK HL HG.
 set(n1:=source_rec_parameter_lift names 1). set(n3:=source_rec_parameter_lift names 3). set(n4:=source_rec_parameter_lift names 4).
 set(A0:=source_parameter_expression n1(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty(S l))(@OC.var OB.sig_empty(S i))(@OC.var OB.sig_empty 0)))).
 set(E0:=E_sf SFEqual(n1 0)(n1(S j))). set(P0:=E_sf SFImpl A0 E0). set(FIRST:=E_sf SFAll P0(CEconst 0)).
 set(GUARD:=E_sf SFMember(n3 2)(n3(S(S(S k))))).
 set(SUCC:=source_parameter_expression n3(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 1)))).
 set(A3:=source_parameter_expression n3(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty(S(S(S l))))(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))).
 set(A4:=source_parameter_expression n4(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty(S(S(S(S l)))))(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 0)))).
 set(BODY:=E_sf SFAnd A4(CEconst 0)). set(EX:=E_sf SFEx BODY(CEconst 0)).
 set(T3:=E_sf SFImpl A3 EX). set(T2:=E_sf SFImpl SUCC T3). set(POINT:=E_sf SFImpl GUARD T2).
 set(ONE:=E_sf SFAll POINT(CEconst 0)). set(TWO:=E_sf SFAll ONE(CEconst 0)). set(SECOND:=E_sf SFAll TWO(CEconst 0)).
 change(code_relation M rho(E_sf SFAnd FIRST SECOND)out)in HG.
 destruct(schema_expression_split M rho SFAnd FIRST SECOND out HG)as(first&second&HFirst&HSecond&HOut).
 destruct(schema_expression_split M rho SFAll P0(CEconst 0)first HFirst)as(p0&z0&HP0&HZ&HFirstAll). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFImpl A0 E0 p0 HP0)as(app0&eq0&HApp0&HEq0&HPoint0).
 assert(N10:code_relation M rho(n1 0)(zeroM M))by reflexivity.
 pose proof(source_rec_parameter_lift_name M names rho 1 i o HI)as N1i.
 pose proof(source_rec_parameter_lift_name M names rho 1 j a HJ)as N1j.
 pose proof(source_rec_parameter_lift_name M names rho 1 l f HL)as N1l.
 pose proof(source_parameter_rec_app M n1 rho(S l)(S i)0 _ _ _ app0 N1l N1i N10 HApp0)as HA0.
 pose proof(proj1(schema_expression_graph M rho SFEqual(n1 0)(n1(S j))(zeroM M)(succM M a)eq0 N10 N1j)HEq0)as HE0.
 assert(HFirstGraph:source_rec_attempt_zero M o a f first)by(exists app0,eq0,p0;auto).
 destruct(schema_expression_split M rho SFAll TWO(CEconst 0)second HSecond)as(two&z0&HTwo&HZ&HOuter). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAll ONE(CEconst 0)two HTwo)as(one&z0&HOne&HZ&HTwoAll). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAll POINT(CEconst 0)one HOne)as(point&z0&HPoint&HZ&HOneAll). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFImpl GUARD T2 point HPoint)as(guard&t2&HGuard&HT2&HPointImpl).
 destruct(schema_expression_split M rho SFImpl SUCC T3 t2 HT2)as(successor&t3&HSuccessor&HT3&H2).
 destruct(schema_expression_split M rho SFImpl A3 EX t3 HT3)as(app3&ex&HApp3&HEx&H3).
 destruct(schema_expression_split M rho SFEx BODY(CEconst 0)ex HEx)as(body&z0&HBody&HZ&HExNode). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAnd A4(CEconst 0)body HBody)as(app4&z0&HApp4&HZ&HBodyNode). change(z0=zeroM M)in HZ. subst z0.
 pose proof(source_rec_parameter_lift_fresh M names rho 3 0 ltac:(lia))as N30.
 pose proof(source_rec_parameter_lift_fresh M names rho 3 1 ltac:(lia))as N31.
 pose proof(source_rec_parameter_lift_fresh M names rho 3 2 ltac:(lia))as N32.
 pose proof(source_rec_parameter_lift_name M names rho 3 k N HK)as N3k.
 pose proof(source_rec_parameter_lift_name M names rho 3 l f HL)as N3l.
 pose proof(source_rec_parameter_lift_name M names rho 4 l f HL)as N4l.
 pose proof(source_rec_parameter_lift_fresh M names rho 4 0 ltac:(lia))as N40.
 pose proof(source_rec_parameter_lift_fresh M names rho 4 3 ltac:(lia))as N43.
 pose proof(proj1(schema_expression_graph M rho SFMember(n3 2)(n3(S(S(S k))))(code_numeral M 2)(source_succ_iter M 3 N)guard N32 N3k)HGuard)as HGuardGraph.
 pose proof(source_parameter_rec_rel2_successor M n3 rho 2 1 _ _ successor N32 N31 HSuccessor)as HSuccessorGraph.
 pose proof(source_parameter_rec_app M n3 rho(S(S(S l)))1 0 _ _ _ app3 N3l N31 N30 HApp3)as HApp3Graph.
 pose proof(source_parameter_rec_app M n4 rho(S(S(S(S l))))3 0 _ _ _ app4 N4l N43 N40 HApp4)as HApp4Graph.
 assert(HSecondGraph:source_rec_attempt_step M(zeroM M)N f second).
 { exists guard,successor,app3,app4. split;[exact HGuardGraph|]. split;[exact HSuccessorGraph|]. split;[exact HApp3Graph|]. split;[exact HApp4Graph|].
   unfold rec_attempt_step_expression,E_sf_all,E_sf_ex. functionality_graph. }
 exists first,second. auto.
Qed.
Print Assumptions source_rec_parameter_lift_name.
Print Assumptions source_rec_parameter_lift_fresh.
Print Assumptions source_parameter_rec_bottom_attempt.
