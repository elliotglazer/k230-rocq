(** Actual finite certificates at any six internally coded variable names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge
 SourceRecursionFactsOld SourceLFixed SourceLNonempty OldZFRProofLift SourceZFRProvability
 SourceFiniteParameters SourceFiniteNameParameters SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_recursion_fact tag :=isolated_formula(old_recursion_fact tag).
Definition source_recursion_fact_graph M tag rho out :=code_relation M rho
 (source_parameter_expression(source_finite_parameter_names 6)(source_recursion_fact tag))out.
Theorem source_zfr_recursion_fact_fixed M tag :source_zfr_provable M(code_numeral M(sf_encode(source_recursion_fact tag))).
Proof. exact(finite_old_zfr_proof_lift M old_L_background(old_recursion_fact tag)old_L_background_valid(old_recursion_fact_proof tag)). Qed.
Theorem source_zfr_recursion_fact_named M tag rho out :source_recursion_fact_graph M tag rho out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_recursion_fact tag)6 rho out
  (proj2(source_zfr_descriptor_provable M _)(source_zfr_recursion_fact_fixed M tag))HG).
Qed.
Theorem source_zfr_recursion_fact_total M tag rho :exists out,source_recursion_fact_graph M tag rho out /\source_zfr_provable M out.
Proof.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 6)(source_recursion_fact tag))rho)as(out&HO).
 exists out. split;[exact HO|exact(source_zfr_recursion_fact_named M tag rho out HO)].
Qed.
Print Assumptions source_zfr_recursion_fact_fixed.
Print Assumptions source_zfr_recursion_fact_named.
Print Assumptions source_zfr_recursion_fact_total.
