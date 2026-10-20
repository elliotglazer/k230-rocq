(** Actual KUpperCore.trace_request: witness closure of B and its trace
    profile imply the literal matrix_request for C. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents
  NumericalContexts NumericalEnvironments NumericalRenaming NumericalSourceFull
  SourceUpperWitnessRecipes SourceWitnessClosedUse SourceWitnessRecipeFunctionality
  SourceTraceProfileShell SourceTraceCompleteRequest SourceInstantiationConstructors
  SourceContextProofHelpers SourceDerivedRules.
Unset Implicit Arguments.

Lemma source_trace_exists_target_wf M cb cc cn c bmem cmem phixp matrixB matrixC exB exC :
  sf_relation M SFMember (zeroM M) (succM M c) cmem ->
  sf_relation M SFAnd bmem phixp matrixB ->sf_relation M SFAnd cmem phixp matrixC ->
  sf_relation M SFEx matrixB (zeroM M) exB ->sf_relation M SFEx matrixC (zeroM M) exC ->
  source_sequent_wf M cb cc cn exB ->source_sequent_wf M cb cc cn exC.
Proof.
  intros HCMem HAndB HAndC HExB HExC [k [HB HC]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx matrixB exB k
    (or_intror eq_refl) HExB) HB) as HMatrixB.
  pose proof (proj2 (proj1 (source_bounded_accept_binary M SFAnd bmem phixp matrixB
    (succM M k) (or_introl eq_refl) HAndB) HMatrixB)) as HPhi.
  set (l:=succM M (addM M k c)).
  assert (HK:coding_lt M k l) by (apply coding_le_add).
  assert (HCL:coding_lt M c l).
  { unfold l. rewrite Arithmetic.add_comm. apply coding_le_add. }
  exists l. split.
  - apply (proj2 (source_bounded_accept_unary M SFEx matrixC exC l (or_intror eq_refl) HExC)).
    apply (proj2 (source_bounded_accept_binary M SFAnd cmem phixp matrixC
      (succM M l) (or_introl eq_refl) HAndC)). split.
    + apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (succM M c)
        cmem (succM M l) (or_introl eq_refl) HCMem)).
      split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel;exact HCL].
    + apply (source_bounded_monotone M phixp (succM M k) (succM M l) HPhi).
      apply coding_lt_succ_cancel. exact (coding_lt_trans M k l (succM M l) HK (coding_lt_succ M l)).
  - apply (context_bounded_monotone M cb cc cn k l HC).
    exact (coding_lt_trans M k l (succM M l) HK (coding_lt_succ M l)).
Qed.

Theorem source_full_upper_trace_request M cb cc cn phi k delta c b profile theta atom matrix body
    closed p pb request :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta matrix ->
  sf_relation M SFMember (zeroM M) (succM M (succM M b)) atom ->
  sf_relation M SFAnd atom matrix body ->sf_relation M SFEx body (zeroM M) theta ->
  source_trace_profile_shell M theta c b profile ->
  source_upper_witness_closed_recipe M phi delta b closed ->
  sf_relation M SFMember p b pb ->source_upper_matrix_request_recipe M phi delta p c request ->
  source_full_prv M cb cc cn closed ->source_full_prv M cb cc cn profile ->
  source_full_prv M cb cc cn pb ->source_full_prv M cb cc cn request.
Proof.
  intros HP HM HA HB HE HProfile HClosed HPb HRequest PC PP PPb.
  destruct (source_full_upper_witness_closed_use_total M cb cc cn phi k delta b closed p pb
    HP HClosed HPb PC PPb) as [requestB [HRequestB PRequestB]].
  destruct HRequestB as [rbB [rcB [valueB [HMapB [HValueB HCodeB]]]]].
  destruct HRequest as [rbC [rcC [valueC [HMapC [HValueC HCodeC]]]]].
  pose proof (source_upper_matrix_request_matrix_unique M phi delta p rbB rcB valueB rbC rcC valueC
    HMapB HValueB HMapC HValueC) as E. subst valueC.
  destruct (source_upper_matrix_request_shell M valueB b requestB HCodeB)
    as (bmem & matrixB & some & exB & HBMem & HMatrixB & HSome & HExB & HImplB).
  destruct (source_upper_matrix_request_shell M valueB c request HCodeC)
    as (cmem & matrixC & some' & exC & HCMem & HMatrixC & HSome' & HExC & HImplC).
  pose proof (sf_relation_functional M SFEx valueB (zeroM M) some' some HSome' HSome) as E. subst some'.
  pose proof (source_full_prv_wellformed M cb cc cn requestB PRequestB) as WRequestB.
  assert (WExC:source_sequent_wf M cb cc cn exC).
  { apply (source_trace_exists_target_wf M cb cc cn c bmem cmem valueB matrixB matrixC exB exC
      HCMem HMatrixB HMatrixC HExB HExC).
    exact (source_wf_binary_right M cb cc cn SFImpl some exB requestB
      (or_intror (or_intror eq_refl)) HImplB WRequestB). }
  assert (WRequest:source_sequent_wf M cb cc cn request).
  { apply (source_wf_binary M cb cc cn SFImpl some exC request (or_intror (or_intror eq_refl)) HImplC).
    - exact (source_wf_binary_left M cb cc cn SFImpl some exB requestB
        (or_intror (or_intror eq_refl)) HImplB WRequestB).
    - exact WExC. }
  destruct WRequestB as [j [HReqBound HCtx]].
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl some exB requestB
    j (or_intror (or_intror eq_refl)) HImplB) HReqBound)) as HSomeBound.
  destruct (environment_cons_total M cb cc cn some) as [ub [uc [un HCons]]].
  assert (HBranch:context_bounded M ub uc un j).
  { apply (proj2 (context_bounded_cons M cb cc cn some ub uc un j HCons)). auto. }
  pose proof (source_full_cons_head M cb cc cn some ub uc un j HCons HSomeBound HBranch) as PSome.
  pose proof (source_full_cons_weaken M cb cc cn some ub uc un j requestB HCons HBranch PRequestB) as PRB.
  pose proof (source_full_modus_ponens M ub uc un some exB requestB HImplB PRB PSome) as PExB.
  pose proof (source_full_cons_weaken M cb cc cn some ub uc un j profile HCons HBranch PP) as PProfile.
  pose proof (source_full_cons_weaken M cb cc cn some ub uc un j pb HCons HBranch PPb) as PInput.
  destruct (sf_relation_total M SFMember (succM M p) (succM M b)) as [input' HInput'].
  pose proof (source_full_upper_trace_request_transfer M ub uc un phi k delta c b profile theta atom matrix body
    p pb input' bmem cmem valueB matrixB matrixC exB exC rbC rcC
    HP HM HA HB HE HProfile HPb HInput' HBMem HCMem HMatrixB HMatrixC HExB HExC
    HMapC HValueC PProfile PInput PExB) as PExC.
  exact (full_source_II M cb cc cn some exC request ub uc un WRequest PExC HCons HImplC).
Qed.

Print Assumptions source_trace_exists_target_wf.
Print Assumptions source_full_upper_trace_request.
