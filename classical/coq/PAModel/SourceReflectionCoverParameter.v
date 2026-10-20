(** Exact finite cofinal-level-cover parameter calibration. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceCofinalGeometry SourceReflectionLevelCoverOld SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters SourceParameterGraphs SourceRecursionPrimitiveRelations.
From OldZFC Require Import Z_L Z_base.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma isolated_reflection_cover_at t u:
 isolated_formula(old_reflection_level_cover t u)=C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)C.var))source_cofinal_cover_predicate.
Proof.
 pose proof(isolated_formula_subst(old_reflection_level_cover(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
  (OC.scons t(OC.scons u OC.var))(C.scons(isolated_term t)(C.scons(isolated_term u)C.var))ltac:(intros[|[|i]];reflexivity))as E.
 assert(HE:OC.subst_form(OC.scons t(OC.scons u OC.var))(old_reflection_level_cover(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))=old_reflection_level_cover t u).
 { unfold old_reflection_level_cover. cbn. autorewrite with fsub. reflexivity. }
 rewrite HE in E. exact E.
Qed.
Theorem source_parameter_reflection_cover M names rho i j K Lb out:
 code_relation M rho(names i)K ->code_relation M rho(names j)Lb ->
 code_relation M rho(source_parameter_expression names(isolated_formula(old_reflection_level_cover(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j))))out ->
 source_cofinal_cover M K Lb out.
Proof.
 intros HK HL HO. rewrite isolated_reflection_cover_at,source_parameter_substitution in HO.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))C.var)).
 assert(HE:forall v x,(v<2)%nat ->
  (code_relation M rho(names(sf_index(sigma v)))x <->code_relation M(source_rec_env2 K Lb)(source_finite_parameter_names 2 v)x)).
 { intros[|[|v]]x HV;try lia.
   - change(code_relation M rho(names i)x<->x=K). split;[intro H;exact(code_relation_functional M _ rho x K H HK)|intros ->;exact HK].
   - change(code_relation M rho(names j)x<->x=Lb). split;[intro H;exact(code_relation_functional M _ rho x Lb H HL)|intros ->;exact HL]. }
 exact(proj1(source_parameter_graph_ext M 2 source_cofinal_cover_predicate source_cofinal_cover_finite_bound
  (fun v=>names(sf_index(sigma v)))(source_finite_parameter_names 2)rho(source_rec_env2 K Lb)HE out)HO).
Qed.
Print Assumptions isolated_reflection_cover_at.
Print Assumptions source_parameter_reflection_cover.
