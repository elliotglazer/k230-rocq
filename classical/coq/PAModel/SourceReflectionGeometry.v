(** Fixed finite ordinal-union and cofinal-level deductions, lifted to
    genuine numerical ZFR proofs at arbitrary PA-model variable names.
    No arbitrary internally coded matrix is lifted as an external formula. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceReflectionUnionOld SourceReflectionLevelCoverOld SourceLFixed SourceLNonempty
  OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_reflection_union_law:=isolated_formula old_reflection_union_law.
Definition source_reflection_level_cover_law:=isolated_formula old_reflection_level_cover_law.
Definition source_reflection_union_expression:=
  source_parameter_expression(source_finite_parameter_names 3)source_reflection_union_law.
Definition source_reflection_level_cover_expression:=
  source_parameter_expression(source_finite_parameter_names 3)source_reflection_level_cover_law.

Theorem source_zfr_reflection_union_geometry M rho out:
  code_relation M rho source_reflection_union_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_reflection_union_law 3 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_reflection_union_law
      old_L_background_valid old_reflection_union_proof).
  - exact HO.
Qed.

Theorem source_zfr_reflection_level_cover M rho out:
  code_relation M rho source_reflection_level_cover_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_reflection_level_cover_law 3 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_reflection_level_cover_law
      old_L_background_valid old_reflection_level_cover_proof).
  - exact HO.
Qed.
Print Assumptions source_zfr_reflection_union_geometry.
Print Assumptions source_zfr_reflection_level_cover.
