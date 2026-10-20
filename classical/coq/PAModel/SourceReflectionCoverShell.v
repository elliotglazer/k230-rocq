(** Actual finite level-cover law for every supplied hierarchy witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceReflectionGeometry SourceReflectionLevelCoverOld SourceReflectionGeometryPredicates SourceReflectionGeometryParameters SourceReflectionCoverParameter
 SourceCofinalGeometry SourceRecursionPrimitiveRelations SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs
 SourceHierarchySyntax SourceHierarchyCalibration SourcePropositionalRebase OldNamedSyntaxBridge SourceFiniteTelescope SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_reflection_cover_shell M K beta Lb:
 exists ordinals union limit known cover law,
 source_cofinal_ordinals M K ordinals /\source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union /\
 source_reflection_geometry_instance M ReflectionLimit(fun _=>beta)limit /\source_LL_instance M beta Lb known /\
 source_cofinal_cover M K Lb cover /\source_finite_telescope M[ordinals;union;limit;known]cover law /\source_zfr_provable M law.
Proof.
 set(rho:=source_rec_env3 K beta Lb). set(names:=source_finite_parameter_names 3).
 destruct(code_relation_total M source_reflection_level_cover_expression rho)as(law&HLaw).
 pose proof(source_zfr_reflection_level_cover M rho law HLaw)as PLaw.
 change(code_relation M rho(E_sf SFImpl(source_parameter_expression names source_cofinal_ordinals_predicate)
  (E_sf SFImpl(source_parameter_expression names(source_reflection_geometry_source ReflectionUnion))
   (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Lim0(@OC.var OB.sig_empty 1))))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))))
     (source_parameter_expression names(isolated_formula(old_reflection_level_cover(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2))))))))law)in HLaw.
 destruct(schema_expression_split M rho SFImpl _ _ law HLaw)as(ordinals&t0&HO&HT0&HI0).
 destruct(schema_expression_split M rho SFImpl _ _ t0 HT0)as(union&t1&HU&HT1&HI1).
 destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(limit&t2&HL&HT2&HI2).
 destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(known&cover&HK&HC&HI3).
 assert(HOrdinals:source_cofinal_ordinals M K ordinals).
 { exact(proj1(source_parameter_graph_ext M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
   names(source_finite_parameter_names 1)rho(fun _=>K)ltac:(intros[|i]v HI;[reflexivity|lia])ordinals)HO). }
 exists ordinals,union,limit,known,cover,law. split;[exact HOrdinals|]. split.
 - exact(source_parameter_reflection_union M names rho 0 1 K beta union eq_refl eq_refl HU).
 - split;[exact(source_parameter_reflection_limit M names rho 1 beta limit eq_refl HL)|].
   split;[exact(source_parameter_LL_instance M names rho 1 2 beta Lb known eq_refl eq_refl HK)|].
   split;[exact(source_parameter_reflection_cover M names rho 0 2 K Lb cover eq_refl eq_refl HC)|]. split;[|exact PLaw].
   exists t0. split;[|exact HI0]. exists t1. split;[|exact HI1]. exists t2. split;[|exact HI2]. exists cover. split;[reflexivity|exact HI3].
Qed.
Print Assumptions source_zfr_reflection_cover_shell.
