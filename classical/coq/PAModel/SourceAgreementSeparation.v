(** Fixed agreement-subset witness at arbitrary internal source names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge
 SourceAgreementSeparationOld OldZFRProofLift SourceZFRProvability SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_agreement_separation_law:=isolated_formula old_agreement_separation_law.
Definition source_agreement_separation_graph M rho out:=code_relation M rho
 (source_parameter_expression(source_finite_parameter_names 3)source_agreement_separation_law)out.
Theorem source_zfr_agreement_separation_fixed M:source_zfr_provable M(code_numeral M(sf_encode source_agreement_separation_law)).
Proof. exact(finite_old_zfr_proof_lift M old_agreement_separation_background old_agreement_separation_law
 old_agreement_separation_background_valid old_agreement_separation_proof). Qed.
Theorem source_zfr_agreement_separation_named M rho out:source_agreement_separation_graph M rho out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_agreement_separation_law 3 rho out
  (proj2(source_zfr_descriptor_provable M _)(source_zfr_agreement_separation_fixed M))HG).
Qed.
Theorem source_zfr_agreement_separation_total M rho:exists out,
 source_agreement_separation_graph M rho out /\source_zfr_provable M out.
Proof.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)source_agreement_separation_law)rho)as(out&HO).
 exists out. split;[exact HO|exact(source_zfr_agreement_separation_named M rho out HO)].
Qed.
Print Assumptions source_zfr_agreement_separation_fixed.
Print Assumptions source_zfr_agreement_separation_named.
Print Assumptions source_zfr_agreement_separation_total.
