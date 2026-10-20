(** Actual finite union geometry law, with every predicate and constructor exposed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation
 SourceReflectionGeometry SourceReflectionUnionOld SourceReflectionGeometryPredicates SourceReflectionGeometryParameters
 SourceCofinalGeometry SourceRecursionPrimitiveRelations SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs
 SourceOrdinalPredicate SourceOrdinalParameterCalibration SourcePropositionalRebase SchemaConstructorBounds
 OldNamedSyntaxBridge SourceFiniteTelescope SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_reflection_union_shell M K beta a:
 exists memberAK ordinals noLast union ordinal limit memberAB subsets r1 r2 result law,
 sf_relation M SFMember a K memberAK /\source_cofinal_ordinals M K ordinals /\
 source_reflection_geometry_instance M ReflectionNoLast(fun _=>K)noLast /\
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union /\
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\
 source_reflection_geometry_instance M ReflectionLimit(fun _=>beta)limit /\sf_relation M SFMember a beta memberAB /\
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets /\
 sf_relation M SFAnd memberAB subsets r2 /\sf_relation M SFAnd limit r2 r1 /\sf_relation M SFAnd ordinal r1 result /\
 source_finite_telescope M[memberAK;ordinals;noLast;union]result law /\source_zfr_provable M law.
Proof.
 set(rho:=source_rec_env3 K beta a). set(names:=source_finite_parameter_names 3).
 destruct(code_relation_total M source_reflection_union_expression rho)as(law&HLaw).
 pose proof(source_zfr_reflection_union_geometry M rho law HLaw)as PLaw.
 change(code_relation M rho(E_sf SFImpl(E_sf SFMember(names 2)(names 0))
  (E_sf SFImpl(source_parameter_expression names source_cofinal_ordinals_predicate)
   (E_sf SFImpl(source_parameter_expression names(source_reflection_geometry_source ReflectionNoLast))
    (E_sf SFImpl(source_parameter_expression names(source_reflection_geometry_source ReflectionUnion))
     (E_sf SFAnd(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
      (E_sf SFAnd(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Lim0(@OC.var OB.sig_empty 1))))
       (E_sf SFAnd(E_sf SFMember(names 2)(names 1))(source_parameter_expression names(source_reflection_geometry_source ReflectionSubsets)))))))))law)in HLaw.
 destruct(schema_expression_split M rho SFImpl _ _ law HLaw)as(memberAK&t0&HMA&HT0&HI0).
 destruct(schema_expression_split M rho SFImpl _ _ t0 HT0)as(ordinals&t1&HO&HT1&HI1).
 destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(noLast&t2&HN&HT2&HI2).
 destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(union&result&HU&HR&HI3).
 destruct(schema_expression_split M rho SFAnd _ _ result HR)as(ordinal&r1&HOrd&HR1&HA0).
 destruct(schema_expression_split M rho SFAnd _ _ r1 HR1)as(limit&r2&HL&HR2&HA1).
 destruct(schema_expression_split M rho SFAnd _ _ r2 HR2)as(memberAB&subsets&HMB&HS&HA2).
 assert(HCofinal:source_cofinal_ordinals M K ordinals).
 { apply(proj1(source_parameter_graph_ext M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
   names(source_finite_parameter_names 1)rho(fun _=>K)ltac:(intros[|i]v HI;[reflexivity|lia])ordinals)HO). }
 assert(HNoLast:source_reflection_geometry_instance M ReflectionNoLast(fun _=>K)noLast).
 { eapply(source_parameter_geometry_instance M ReflectionNoLast names rho(fun _=>K)noLast);[|exact HN]. intros[|i]HI;[reflexivity|cbn in HI;lia]. }
 assert(HUnion:source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union).
 { eapply(source_parameter_geometry_instance M ReflectionUnion names rho(source_rec_env2 K beta)union);[|exact HU]. intros[|[|i]]HI;try reflexivity;cbn in HI;lia. }
 assert(HSubsets:source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets).
 { eapply(source_parameter_geometry_instance M ReflectionSubsets names rho(source_rec_env2 K beta)subsets);[|exact HS]. intros[|[|i]]HI;try reflexivity;cbn in HI;lia. }
 exists memberAK,ordinals,noLast,union,ordinal,limit,memberAB,subsets,r1,r2,result,law.
 split;[exact(proj1(schema_expression_graph M rho SFMember(names 2)(names 0)a K memberAK eq_refl eq_refl)HMA)|].
 split;[exact HCofinal|]. split;[exact HNoLast|]. split;[exact HUnion|].
 split;[exact(source_parameter_ordinal_instance M names rho 1 beta ordinal eq_refl HOrd)|].
 split;[exact(source_parameter_reflection_limit M names rho 1 beta limit eq_refl HL)|].
 split;[exact(proj1(schema_expression_graph M rho SFMember(names 2)(names 1)a beta memberAB eq_refl eq_refl)HMB)|].
 split;[exact HSubsets|]. split;[exact HA2|]. split;[exact HA1|]. split;[exact HA0|]. split;[|exact PLaw].
 exists t0. split;[|exact HI0]. exists t1. split;[|exact HI1]. exists t2. split;[|exact HI2]. exists result. split;[reflexivity|exact HI3].
Qed.
Print Assumptions source_zfr_reflection_union_shell.
