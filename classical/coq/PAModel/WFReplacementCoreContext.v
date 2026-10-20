(** Construct a genuine internally finite core context containing the
    ambient Replacement axiom and an actual fixed WF-closure derivation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalSourceFull
  NumericalZFCAxioms NumericalZFCClosure NumericalCoreAxioms
  SchemaRenamingDescriptors SetSchemaConstructors NumericalSetClosure
  CoreConsistencyReduction SourceContextTransport SourceProofWeakening SourceClosedPrefixes
  WFClosureFiniteBridge NumericalWFCoreFixed.
Unset Implicit Arguments.
Local Opaque source_wf_closure_code.

Theorem source_wf_replacement_core_background M matrix n ax :
  numerical_replacement_instance M matrix n ax ->
  exists ma mb mc rawopen b c l,
    schema_renaming M RepA matrix ma /\schema_renaming M RepB matrix mb /\
    schema_renaming M RepC matrix mc /\sf_replacement_constructor M ma mb mc rawopen /\
    source_core_context M b c l /\context_bounded M b c l (zeroM M) /\
    source_full_prv M b c l (source_wf_closure_code M) /\source_full_prv M b c l rawopen.
Proof.
  intro HInstance.
  pose proof (numerical_replacement_instance_closed M matrix n ax HInstance) as HAxBound.
  assert (HAxiom:numerical_zfc_core_source_axiom M ax).
  { right;right. apply numerical_closed_replacement_redundant. now exists matrix,n. }
  destruct HInstance as [_ [ma [mb [mc [rawopen [HMA [HMB [HMC [HRaw HPrefix]]]]]]]]].
  destruct (numerical_wf_closure_core M) as [b [c [l [HCore PClosure]]]].
  destruct (environment_cons_total M b c l ax) as [u [v [j HCons]]].
  assert (HNewCore:source_core_context M u v j).
  { intros a HA. apply (proj1 (context_member_cons M b c l ax u v j a HCons)) in HA.
    destruct HA as [<-|HA];[exact HAxiom|exact (HCore a HA)]. }
  pose proof (source_core_context_closed M u v j HNewCore) as HC.
  assert (HI:context_included M b c l u v j).
  { intros a HA. apply (proj2 (context_member_cons M b c l ax u v j a HCons)). now right. }
  assert (PAxiom:source_full_prv M u v j ax).
  { apply (full_source_Ctx M u v j ax).
    - exists (zeroM M). now split.
    - apply (proj2 (context_member_cons M b c l ax u v j ax HCons)). now left. }
  exists ma,mb,mc,rawopen,u,v,j. repeat split;try assumption.
  - exact (source_full_prv_weaken_bounded M b c l u v j _ (zeroM M) PClosure HI HC).
  - exact (source_full_prefix_eliminate M u v j n rawopen ax HC HPrefix PAxiom).
Qed.

Print Assumptions source_wf_replacement_core_background.
