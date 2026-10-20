(** Literal finite parameter calibration for Union0 and Lim0 at named roles. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteParameterComposition SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations.
From OldZFC Require Z_base.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma isolated_reflection_limit_at t:
 isolated_formula(OldZFC.Z_base.Lim0 t)=C.subst_form(C.scons(isolated_term t)C.var)(source_reflection_geometry_source ReflectionLimit).
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Lim0(@OC.var OB.sig_empty 0))
  (OC.scons t OC.var)(C.scons(isolated_term t)C.var)ltac:(intros[|i];reflexivity))as E.
 rewrite OldZFC.Z_base.Lim0_subst in E. exact E.
Qed.
Lemma isolated_reflection_union_at t u:
 isolated_formula(OldZFC.Z_base.Union0 t u)=C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)C.var))(source_reflection_geometry_source ReflectionUnion).
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Union0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
  (OC.scons t(OC.scons u OC.var))(C.scons(isolated_term t)(C.scons(isolated_term u)C.var))ltac:(intros[|[|i]];reflexivity))as E.
 rewrite OldZFC.Z_base.Union0_subst in E. exact E.
Qed.
Theorem source_parameter_reflection_limit M names rho i name out:
 code_relation M rho(names i)name ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Lim0(@OC.var OB.sig_empty i))))out ->
 source_reflection_geometry_instance M ReflectionLimit(fun _=>name)out.
Proof.
 intros HName HO. rewrite isolated_reflection_limit_at,source_parameter_substitution in HO.
 eapply(source_parameter_geometry_instance M ReflectionLimit(fun j=>names(sf_index((C.scons(isolated_term(@OC.var OB.sig_empty i))C.var)j)))rho(fun _=>name)out);[|exact HO].
 intros[|j]HJ;[exact HName|cbn in HJ;lia].
Qed.
Theorem source_parameter_reflection_union M names rho i j K beta out:
 code_relation M rho(names i)K ->code_relation M rho(names j)beta ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Union0(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j))))out ->
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)out.
Proof.
 intros HK HB HO. rewrite isolated_reflection_union_at,source_parameter_substitution in HO.
 eapply(source_parameter_geometry_instance M ReflectionUnion(fun v=>names(sf_index((C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))C.var))v)))rho(source_rec_env2 K beta)out);[|exact HO].
 intros[|[|v]]HV;[exact HK|exact HB|cbn in HV;lia].
Qed.
Print Assumptions isolated_reflection_limit_at.
Print Assumptions isolated_reflection_union_at.
Print Assumptions source_parameter_reflection_limit.
Print Assumptions source_parameter_reflection_union.
