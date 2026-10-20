(** The witness-preserving part of KUpperCore.trace_request. Every syntax
    compatibility premise is an actual source constructor or substitution
    graph. The source proof of the target request is constructed here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming NumericalRenamingMaps NumericalInstantiation
  SourceTracePointRules SourceTraceProfileShell SourcePropositionalTemplates
  SourceSeparationSubset SourceInstantiationConstructors SourceConjunctionRules
  SourceDerivedRules SourceSequents NumericalSourceFull SourceProofRenaming
  SourceContextProofHelpers SourceExistentialMap SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_full_trace_shell_member M cb cc cn theta c b profile x p left right some
    inner witness pb phixp :
  source_trace_profile_shell M theta c b profile ->
  sf_relation M SFMember x c left -> sf_relation M SFMember x b right ->
  numerical_instantiation M theta x some -> sf_relation M SFEx inner (zeroM M) some ->
  numerical_instantiation M inner p witness -> sf_relation M SFAnd pb phixp witness ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn right ->
  source_full_prv M cb cc cn pb -> source_full_prv M cb cc cn phixp ->
  source_full_prv M cb cc cn left.
Proof.
  intros HProfile HL HR HS HEx HInst HPair PP PR PPb PPhi.
  destruct (code_relation_total M (source_prop_expression separation_point_template)
    (schema_env3 left right some)) as [point HPoint].
  pose proof (source_full_trace_shell_point M cb cc cn theta c b profile x left right some point
    HProfile HL HR HS HPoint PP) as PPoint.
  destruct (source_trace_point_unpack M left right some point HPoint)
    as [rhs [forward [reverse [HAnd [HF [HV HI]]]]]].
  pose proof (source_full_conjunction_right M cb cc cn forward reverse point HI PPoint) as PV.
  assert (WSome:source_sequent_wf M cb cc cn some).
  { apply (source_wf_binary_right M cb cc cn SFAnd right some rhs (or_introl eq_refl) HAnd).
    exact (source_wf_binary_left M cb cc cn SFImpl rhs left reverse
      (or_intror (or_intror eq_refl)) HV (source_full_prv_wellformed M cb cc cn reverse PV)). }
  assert (PWitness:source_full_prv M cb cc cn witness).
  { apply (full_source_CI M cb cc cn pb phixp witness);[|exact PPb|exact PPhi|exact HPair].
    exact (source_wf_binary M cb cc cn SFAnd pb phixp witness (or_introl eq_refl) HPair
      (source_full_prv_wellformed M cb cc cn pb PPb)
      (source_full_prv_wellformed M cb cc cn phixp PPhi)). }
  pose proof (full_source_ExI M cb cc cn inner some p witness WSome PWitness HEx HInst) as PSome.
  assert (PRhs:source_full_prv M cb cc cn rhs).
  { apply (full_source_CI M cb cc cn right some rhs);[|exact PR|exact PSome|exact HAnd].
    exact (source_wf_binary M cb cc cn SFAnd right some rhs (or_introl eq_refl) HAnd
      (source_full_prv_wellformed M cb cc cn right PR) WSome). }
  exact (source_full_modus_ponens M cb cc cn rhs left reverse HV PV PRhs).
Qed.

Theorem source_full_trace_request_map M cb cc cn theta c b profile profile'
    theta' p input input' bmem cmem phixp matrixB matrixC exB exC
    some inner witness sb sc ub uc un shifted :
  source_trace_profile_shell M theta c b profile ->
  source_formula_shift M profile profile' ->
  source_trace_profile_shell M theta' (succM M c) (succM M b) profile' ->
  sf_relation M SFMember p b input ->
  sf_relation M SFMember (succM M p) (succM M b) input' ->
  sf_relation M SFMember (zeroM M) (succM M b) bmem ->
  sf_relation M SFMember (zeroM M) (succM M c) cmem ->
  sf_relation M SFAnd bmem phixp matrixB -> sf_relation M SFAnd cmem phixp matrixC ->
  sf_relation M SFEx matrixB (zeroM M) exB -> sf_relation M SFEx matrixC (zeroM M) exC ->
  numerical_instantiation M theta' (zeroM M) some ->
  sf_relation M SFEx inner (zeroM M) some ->
  numerical_instantiation M inner (succM M p) witness ->
  sf_relation M SFAnd input' phixp witness ->
  context_shift M cb cc cn sb sc -> environment_cons M sb sc cn matrixB ub uc un ->
  source_formula_shift M exC shifted -> source_sequent_wf M cb cc cn exC ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn input ->
  source_full_prv M cb cc cn exB -> source_full_prv M cb cc cn exC.
Proof.
  intros HProfile HProfileShift HProfile' HInput HInput' HBMem HCMem HMatrixB HMatrixC
    HExB HExC HSome HSomeEx HValue HPair HShift HCons HExShift HWF PP PI PEx.
  destruct (source_full_prv_wellformed M cb cc cn exB PEx) as [k [HBB HCB]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx matrixB exB k
    (or_intror eq_refl) HExB) HBB) as HMatrixBBound.
  assert (HBranch:context_bounded M ub uc un (succM M k)).
  { apply (proj2 (context_bounded_cons M sb sc cn matrixB ub uc un (succM M k) HCons)).
    split;[exact HMatrixBBound|]. exact (context_shift_preserves_bound M cb cc cn sb sc k HShift HCB). }
  assert (PProfile':source_full_prv M ub uc un profile').
  { apply (source_full_cons_weaken M sb sc cn matrixB ub uc un (succM M k) profile' HCons HBranch).
    exact (source_full_prv_renaming M cb cc cn profile (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) sb sc profile' PP HShift HProfileShift). }
  assert (RInput:numerical_renaming M input (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) input').
  { apply (proj2 (numerical_renaming_member M p b input (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) input' HInput)).
    exists (succM M p),(succM M b). split;[apply context_shift_lookup;reflexivity|].
    split;[apply context_shift_lookup;reflexivity|exact HInput']. }
  assert (PInput':source_full_prv M ub uc un input').
  { apply (source_full_cons_weaken M sb sc cn matrixB ub uc un (succM M k) input' HCons HBranch).
    exact (source_full_prv_renaming M cb cc cn input (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) sb sc input' PI HShift RInput). }
  pose proof (source_full_cons_head M sb sc cn matrixB ub uc un (succM M k)
    HCons HMatrixBBound HBranch) as PMatrixB.
  pose proof (source_full_conjunction_left M ub uc un bmem phixp matrixB HMatrixB PMatrixB) as PBMem.
  pose proof (source_full_conjunction_right M ub uc un bmem phixp matrixB HMatrixB PMatrixB) as PPhi.
  pose proof (source_full_trace_shell_member M ub uc un theta' (succM M c) (succM M b)
    profile' (zeroM M) (succM M p) cmem bmem some inner witness input' phixp
    HProfile' HCMem HBMem HSome HSomeEx HValue HPair PProfile' PBMem PInput' PPhi) as PCMem.
  assert (PMatrixC:source_full_prv M ub uc un matrixC).
  { apply (full_source_CI M ub uc un cmem phixp matrixC);[|exact PCMem|exact PPhi|exact HMatrixC].
    exact (source_wf_binary M ub uc un SFAnd cmem phixp matrixC (or_introl eq_refl) HMatrixC
      (source_full_prv_wellformed M ub uc un cmem PCMem)
      (source_full_prv_wellformed M ub uc un phixp PPhi)). }
  exact (source_full_exists_map M cb cc cn matrixB matrixC exB exC sb sc ub uc un shifted
    HWF HExB HExC HShift HCons HExShift PEx PMatrixC).
Qed.

Print Assumptions source_full_trace_shell_member.
Print Assumptions source_full_trace_request_map.
