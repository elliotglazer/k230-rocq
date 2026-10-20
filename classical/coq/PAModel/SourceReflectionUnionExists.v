(** Actual union-carrier existence at every model-valued K variable. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldZFRProofLift
 SourceLFixed SourceLNonempty SourceReflectionUnionExistsOld SourceReflectionGeometryPredicates SourceReflectionGeometryParameters
 SourceRecursionPrimitiveRelations SourceFiniteParameters SourceFiniteNameParameters SourceRecursionParameterCalibration
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceWFSeparationConstructor.
Unset Implicit Arguments.
Definition source_reflection_union_exists_source:=isolated_formula old_reflection_union_exists.
Definition source_reflection_union_exists_expression:=source_parameter_expression(source_finite_parameter_names 1)source_reflection_union_exists_source.
Theorem source_zfr_reflection_union_exists M K:exists body out,
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2(succM M K)(zeroM M))body /\
 sf_relation M SFEx body(zeroM M)out /\source_zfr_provable M out.
Proof.
 set(names:=source_finite_parameter_names 1). set(rho:=fun(_ :nat)=>K).
 destruct(code_relation_total M source_reflection_union_exists_expression rho)as(out&HO).
 assert(PO:source_zfr_provable M out).
 { apply(proj1(source_zfr_descriptor_provable M out)).
   apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_reflection_union_exists_source 1 rho out).
   - apply(proj2(source_zfr_descriptor_provable M _)). exact(finite_old_zfr_proof_lift M old_L_background old_reflection_union_exists old_L_background_valid old_reflection_union_exists_proof).
   - exact HO. }
 change(code_relation M rho(E_sf SFEx(source_parameter_expression(source_parameter_up names)
  (isolated_formula(OldZFC.Z_base.Union0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0))))(CEconst 0))out)in HO.
 destruct(schema_expression_quantifier_split M rho SFEx _ out HO)as(body&HB&HEx).
 exists body,out. split;[|auto].
 exact(source_parameter_reflection_union M(source_parameter_up names)rho 1 0(succM M K)(zeroM M)body
  (source_parameter_up_name M names rho 0 K eq_refl)eq_refl HB).
Qed.
Print Assumptions source_zfr_reflection_union_exists.
