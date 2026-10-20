(** Ordinary proof projections from the exact eight-conjunct geometry payload. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes NumericalSourceFull SourceConjunctionRules SourcePropositionalTemplates
 SourcePropositionalRebase SourceReflectionGeometryPoint SourceCofinalGeometry SourceReflectionKF SourceReflectionGeometryPredicates
 SourceRecursionPrimitiveRelations SourceOrdinalPredicate NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_full_reflection_geometry_leaves M m o kf u ob l mb s out b c n:
 code_relation M(source_reflection_geometry_values m o kf u ob l mb s)(source_prop_expression source_reflection_geometry_payload)out ->
 source_full_prv M b c n out ->
 source_full_prv M b c n m /\source_full_prv M b c n o /\source_full_prv M b c n kf /\source_full_prv M b c n u /\
 source_full_prv M b c n ob /\source_full_prv M b c n l /\source_full_prv M b c n mb /\source_full_prv M b c n s.
Proof.
 intros HG POut. set(rho:=source_reflection_geometry_values m o kf u ob l mb s).
 change(code_relation M rho(source_prop_expression source_reflection_geometry_payload)out)in HG.
 cbn[source_reflection_geometry_payload source_prop_expression]in HG.
 destruct(schema_expression_split M rho SFAnd _ _ out HG)as(v0&r0&HV0&HR0&HA0). change(v0=m)in HV0. subst v0.
 pose proof(source_full_conjunction_left M b c n m r0 out HA0 POut)as PM.
 pose proof(source_full_conjunction_right M b c n m r0 out HA0 POut)as PR0.
 destruct(schema_expression_split M rho SFAnd _ _ r0 HR0)as(v1&r1&HV1&HR1&HA1). change(v1=o)in HV1. subst v1.
 pose proof(source_full_conjunction_left M b c n o r1 r0 HA1 PR0)as PO.
 pose proof(source_full_conjunction_right M b c n o r1 r0 HA1 PR0)as PR1.
 destruct(schema_expression_split M rho SFAnd _ _ r1 HR1)as(v2&r2&HV2&HR2&HA2). change(v2=kf)in HV2. subst v2.
 pose proof(source_full_conjunction_left M b c n kf r2 r1 HA2 PR1)as PKF.
 pose proof(source_full_conjunction_right M b c n kf r2 r1 HA2 PR1)as PR2.
 destruct(schema_expression_split M rho SFAnd _ _ r2 HR2)as(v3&r3&HV3&HR3&HA3). change(v3=u)in HV3. subst v3.
 pose proof(source_full_conjunction_left M b c n u r3 r2 HA3 PR2)as PU.
 pose proof(source_full_conjunction_right M b c n u r3 r2 HA3 PR2)as PR3.
 destruct(schema_expression_split M rho SFAnd _ _ r3 HR3)as(v4&r4&HV4&HR4&HA4). change(v4=ob)in HV4. subst v4.
 pose proof(source_full_conjunction_left M b c n ob r4 r3 HA4 PR3)as POB.
 pose proof(source_full_conjunction_right M b c n ob r4 r3 HA4 PR3)as PR4.
 destruct(schema_expression_split M rho SFAnd _ _ r4 HR4)as(v5&r5&HV5&HR5&HA5). change(v5=l)in HV5. subst v5.
 pose proof(source_full_conjunction_left M b c n l r5 r4 HA5 PR4)as PL.
 pose proof(source_full_conjunction_right M b c n l r5 r4 HA5 PR4)as PR5.
 destruct(schema_expression_split M rho SFAnd _ _ r5 HR5)as(v6&v7&HV6&HV7&HA6). change(v6=mb)in HV6. change(v7=s)in HV7. subst v6 v7.
 pose proof(source_full_conjunction_left M b c n mb s r5 HA6 PR5)as PMB.
 pose proof(source_full_conjunction_right M b c n mb s r5 HA6 PR5)as PS.
 auto 15.
Qed.
Theorem source_full_reflection_geometry_point_facts M domain level sb sc count a K beta out b c n:
 source_reflection_geometry_point M domain level sb sc count a K beta out ->source_full_prv M b c n out ->
 exists m o kf u ob l mb s,
 sf_relation M SFMember a K m /\source_cofinal_ordinals M K o /\source_reflection_KF M domain level sb sc count K kf /\
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)u /\numerical_instantiation M(source_ordinal_predicate_code M)beta ob /\
 source_reflection_geometry_instance M ReflectionLimit(fun _=>beta)l /\sf_relation M SFMember a beta mb /\
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)s /\
 source_full_prv M b c n m /\source_full_prv M b c n o /\source_full_prv M b c n kf /\source_full_prv M b c n u /\
 source_full_prv M b c n ob /\source_full_prv M b c n l /\source_full_prv M b c n mb /\source_full_prv M b c n s.
Proof.
 intros(m&o&kf&u&ob&l&mb&s&HM&HO&HKF&HU&HOB&HL&HMB&HS&HOut)POut.
 exists m,o,kf,u,ob,l,mb,s. do 8(split;[assumption|]).
 exact(source_full_reflection_geometry_leaves M m o kf u ob l mb s out b c n HOut POut).
Qed.
Print Assumptions source_full_reflection_geometry_leaves.
Print Assumptions source_full_reflection_geometry_point_facts.
