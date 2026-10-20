(** Finite three-role formulas follow an arbitrary internal role map.
    Unused parameter entries may move, so only the actual finite bound is used. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterNamedBinder SourceParameterGraphs
 SourceParameterIdentityCalibration SourceParameterRenamingTransport SourceLocalNamedClosureExistence
 NumericalRenamingMaps NumericalRenaming.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.
Theorem source_local_three_roles_renaming M(phi:sf_form)A S C rb rc rn result:
 bounded 3 phi ->renaming_lookup M rb rc rn(zeroM M)(code_numeral M 0)A ->
 renaming_lookup M rb rc rn(zeroM M)(code_numeral M 1)S ->
 renaming_lookup M rb rc rn(zeroM M)(code_numeral M 2)C ->
 code_relation M(local_closure_roles A S C)(source_parameter_expression(source_finite_parameter_names 3)phi)result ->
 numerical_renaming M(code_numeral M(sf_encode phi))rb rc rn(zeroM M)result.
Proof.
 intros BP H0 H1 H2 HO.
 assert(HId:code_relation M(fun i=>code_numeral M i)
  (source_parameter_expression(source_finite_parameter_names 3)phi)(code_numeral M(sf_encode phi))).
 { apply source_parameter_identity_calibration. intro i. unfold source_finite_parameter_names.
   destruct(Nat.ltb i 3);reflexivity. }
 apply(source_parameter_renaming_transport M 3 phi BP(source_finite_parameter_names 3)(source_finite_parameter_names 3)
  (fun i=>code_numeral M i)(local_closure_roles A S C)rb rc rn(zeroM M)_ result);[|exact HId|exact HO].
 intros i x y HI HX HY.
 pose proof(finite_parameter_name_graph M 3(fun i=>code_numeral M i)i HI)as GX.
 pose proof(finite_parameter_name_graph M 3(local_closure_roles A S C)i HI)as GY.
 rewrite(code_relation_functional M _ _ x(code_numeral M i)HX GX).
 rewrite(code_relation_functional M _ _ y(local_closure_roles A S C i)HY GY).
 destruct i as[|[|[|i]]];try lia;exact H0||exact H1||exact H2.
Qed.
Print Assumptions source_local_three_roles_renaming.
