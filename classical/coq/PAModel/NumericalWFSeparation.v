(** Uniform WF Separation image, including nonstandard schema matrices and
    nonstandard lengths of parameter closure. No schema-image premise remains. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalSourceFull
  NumericalCoreAxioms NumericalZFCAxioms NumericalZFCClosure NumericalSetClosure
  SchemaRenamingDescriptors SchemaRenamingBounds SetSchemaConstructors
  SourceRelativization SourceRelativizationBounds SourceSchemaRelativization
  SourceRelativeSchemaInputs SourceRelativeSchemaConstructors QuotationSchemaSkeleton
  CoreConsistencyReduction SourceProofWeakening SourceContextTransport
  SourceClosedPrefixes SourceGuardedPrefixes NumericalWFFoundation WFSubsetCore
  SourceWFSeparationConstructor.
Unset Implicit Arguments.
Local Opaque source_wf_domain_code source_wf_subset_code.

Theorem numerical_WF_separation_image M f rf :
  numerical_closed_separation M f ->
  source_relativization M (source_wf_domain_code M) f rf ->
  source_core_provable M rf.
Proof.
  intros [_ [phi [n [HPhi [body [open_code [HBody [HOpen HClosed]]]]]]]] HImage.
  destruct (source_relativization_total M (source_wf_domain_code M) phi) as [rphi HRPhi].
  pose proof (numerical_wf_domain_bounded M) as HD.
  destruct (source_relative_separation_input M (source_wf_domain_code M) phi rphi n HD HPhi HRPhi)
    as [ax [HInstance HAxiom]].
  pose proof (numerical_separation_instance_closed M rphi n ax HInstance) as HAxiomBound.
  destruct HInstance as [HRPhiBound [rbody [rawopen [HRBody [HRawOpen HRawClosed]]]]].
  pose proof (source_relativization_schema_renaming M (source_wf_domain_code M) phi rphi
    SepBody body rbody HD HRPhi HBody HRBody) as HRBodyImage.
  pose proof (schema_separation_bound M rphi rbody n HRPhiBound HRBody) as HRBodyBound.
  destruct (code_relation_total M (skeleton_relative_code separation_skeleton)
    (skeleton_relative_environment (source_wf_domain_code M) (fun _=>rbody))) as [targetopen HTarget].
  assert (HTargetConstructor:sf_relative_separation_constructor M (source_wf_domain_code M) rbody targetopen)
    by exact HTarget.
  pose proof (source_separation_constructor_relativization M (source_wf_domain_code M)
    body rbody open_code targetopen HRBodyImage HOpen HTargetConstructor) as HOpenImage.
  destruct (numerical_wf_subset_core M) as [b [c [l [HCore PSubset]]]].
  destruct (environment_cons_total M b c l ax) as [u [v [j HCons]]].
  assert (HNewCore:source_core_context M u v j).
  { intros a HA. apply (proj1 (context_member_cons M b c l ax u v j a HCons)) in HA.
    destruct HA as [<-|HA];[exact HAxiom|exact (HCore a HA)]. }
  pose proof (source_core_context_closed M u v j HNewCore) as HNewBound.
  assert (HI:context_included M b c l u v j).
  { intros a HA. apply (proj2 (context_member_cons M b c l ax u v j a HCons)). now right. }
  assert (PSubsetNew:source_full_prv M u v j (source_wf_subset_code M)).
  { exact (source_full_prv_weaken_bounded M b c l u v j _ (zeroM M) PSubset HI HNewBound). }
  assert (PAxiom:source_full_prv M u v j ax).
  { apply (full_source_Ctx M u v j ax).
    - exists (zeroM M). now split.
    - apply (proj2 (context_member_cons M b c l ax u v j ax HCons)). now left. }
  pose proof (source_full_prefix_eliminate M u v j n rawopen ax HNewBound HRawClosed PAxiom) as PRawOpen.
  pose proof (source_full_WF_separation_open M u v j n rbody rawopen targetopen
    HNewBound HRBodyBound HRawOpen HTargetConstructor PSubsetNew PRawOpen) as PTargetOpen.
  exists u,v,j. split;[exact HNewCore|].
  exact (source_full_guarded_prefix M (source_wf_domain_code M) u v j open_code targetopen
    HNewBound HD HOpenImage n f rf HClosed HImage PTargetOpen).
Qed.

Print Assumptions numerical_WF_separation_image.
