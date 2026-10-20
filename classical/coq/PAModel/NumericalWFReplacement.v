(** Uniform WF Replacement image. The matrix, all schema renamings, and
    the number of closed parameters range over the arbitrary PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull NumericalZFCAxioms NumericalSetClosure
  SchemaRenamingDescriptors SchemaRenamingBounds SetSchemaConstructors
  SourceRelativization SourceRelativizationBounds SourceSchemaRelativization
  SourceRelativeSchemaInputs SourceRelativeSchemaConstructors QuotationSchemaSkeleton
  CoreConsistencyReduction SourceGuardedPrefixes NumericalWFFoundation WFClosureFiniteBridge
  WFReplacementCoreContext SourceWFReplacementConstructor.
Unset Implicit Arguments.
Local Opaque source_wf_domain_code source_wf_closure_code.

Theorem numerical_WF_replacement_image M f rf :
  numerical_closed_replacement M f ->
  source_relativization M (source_wf_domain_code M) f rf ->source_core_provable M rf.
Proof.
  intros [_ [phi [n [HPhi [bodyA [bodyB [bodyC [open_code [HBodyA [HBodyB [HBodyC [HOpen HClosed]]]]]]]]]]]] HImage.
  destruct (source_relativization_total M (source_wf_domain_code M) phi) as [rphi HRPhi].
  pose proof (numerical_wf_domain_bounded M) as HD.
  pose proof (source_relativization_preserves_bound M phi (source_wf_domain_code M)
    (succM M (succM M n)) rphi HD HPhi HRPhi) as HRPhiBound.
  destruct (source_relative_replacement_input M (source_wf_domain_code M) phi rphi n HD HPhi HRPhi)
    as [matrix [ax [HMatrix [HInstance HAxiom]]]].
  destruct (source_wf_replacement_core_background M matrix n ax HInstance)
    as [ma [mb [mc [rawopen [b [c [l [HMA [HMB [HMC [HRaw [HCore [HC [PClosure PRaw]]]]]]]]]]]]]].
  destruct (schema_renaming_total M RepA rphi) as [ra HRA].
  destruct (schema_renaming_total M RepB rphi) as [rb HRB].
  destruct (schema_renaming_total M RepC rphi) as [rc HRC].
  pose proof (source_relativization_schema_renaming M (source_wf_domain_code M) phi rphi
    RepA bodyA ra HD HRPhi HBodyA HRA) as HImageA.
  pose proof (source_relativization_schema_renaming M (source_wf_domain_code M) phi rphi
    RepB bodyB rb HD HRPhi HBodyB HRB) as HImageB.
  pose proof (source_relativization_schema_renaming M (source_wf_domain_code M) phi rphi
    RepC bodyC rc HD HRPhi HBodyC HRC) as HImageC.
  pose proof (schema_replacement_a_bound M rphi ra n HRPhiBound HRA) as HABound.
  pose proof (schema_replacement_b_bound M rphi rb n HRPhiBound HRB) as HBBound.
  pose proof (schema_replacement_c_bound M rphi rc n HRPhiBound HRC) as HCBound.
  destruct (code_relation_total M (skeleton_relative_code replacement_skeleton)
    (skeleton_relative_environment (source_wf_domain_code M) (schema_env3 ra rb rc)))
    as [targetopen HTarget].
  assert (HTargetConstructor:sf_relative_replacement_constructor M (source_wf_domain_code M) ra rb rc targetopen)
    by exact HTarget.
  pose proof (source_replacement_constructor_relativization M (source_wf_domain_code M)
    bodyA bodyB bodyC ra rb rc open_code targetopen HImageA HImageB HImageC HOpen HTargetConstructor)
    as HOpenImage.
  pose proof (source_full_WF_replacement_open M b c l n rphi matrix ra rb rc ma mb mc rawopen targetopen
    HC HABound HBBound HCBound HMatrix HMA HMB HMC HRA HRB HRC HRaw HTargetConstructor PClosure PRaw)
    as PTargetOpen.
  exists b,c,l. split;[exact HCore|].
  exact (source_full_guarded_prefix M (source_wf_domain_code M) b c l open_code targetopen
    HC HD HOpenImage n f rf HClosed HImage PTargetOpen).
Qed.

Print Assumptions numerical_WF_replacement_image.
