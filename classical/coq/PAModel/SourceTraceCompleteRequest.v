(** Complete trace-request witness transfer. Context representations,
    shifted profiles, witness-branch proofs and intermediate matrix
    instantiations are constructed rather than supplied as proof premises. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenamingMaps NumericalRenaming SourceRoleReopening
  NumericalSubstitution SourceTraceProfileShell SourceTraceGenericMember SourceTraceDeltaShift
  SourceProofRenaming SourceContextProofHelpers SourceConjunctionRules SourceInstantiationConstructors
  SourceSequents SourceTraceBounds SourceContextTransport NumericalSourceFull SourceExistentialMap SourceQuantifierRules.
Unset Implicit Arguments.

Lemma source_trace_request_target_wf M cb cc cn c bmem cmem phixp matrixB matrixC exB exC :
  sf_relation M SFMember (zeroM M) (succM M c) cmem ->
  sf_relation M SFAnd bmem phixp matrixB ->sf_relation M SFAnd cmem phixp matrixC ->
  sf_relation M SFEx matrixB (zeroM M) exB ->sf_relation M SFEx matrixC (zeroM M) exC ->
  source_full_prv M cb cc cn exB ->source_sequent_wf M cb cc cn exC.
Proof.
  intros HCMem HAndB HAndC HExB HExC PEx.
  destruct (source_full_prv_wellformed M cb cc cn exB PEx) as [k [HB HC]].
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

Theorem source_full_upper_trace_request_transfer M cb cc cn phi k delta c b profile theta atom matrix body
    p input input' bmem cmem phixp matrixB matrixC exB exC rb rc :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta matrix ->
  sf_relation M SFMember (zeroM M) (succM M (succM M b)) atom ->
  sf_relation M SFAnd atom matrix body ->sf_relation M SFEx body (zeroM M) theta ->
  source_trace_profile_shell M theta c b profile ->
  sf_relation M SFMember p b input ->sf_relation M SFMember (succM M p) (succM M b) input' ->
  sf_relation M SFMember (zeroM M) (succM M b) bmem ->
  sf_relation M SFMember (zeroM M) (succM M c) cmem ->
  sf_relation M SFAnd bmem phixp matrixB ->sf_relation M SFAnd cmem phixp matrixC ->
  sf_relation M SFEx matrixB (zeroM M) exB ->sf_relation M SFEx matrixC (zeroM M) exC ->
  source_role_reopening M (succM M p) (zeroM M) rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) (succM M delta) phixp ->
  source_full_prv M cb cc cn profile ->source_full_prv M cb cc cn input ->
  source_full_prv M cb cc cn exB ->source_full_prv M cb cc cn exC.
Proof.
  intros HP HM HA HB HE HProfile HInput HInput' HBMem HCMem HMatrixB HMatrixC
    HExB HExC HMap HValue PP PI PEx.
  destruct (context_shift_total M cb cc cn) as [sb [sc HShift]].
  destruct (environment_cons_total M sb sc cn matrixB) as [ub [uc [un HCons]]].
  destruct (numerical_renaming_total M profile (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1)) as [profile' HProfileShift].
  destruct (source_trace_delta_profile_shift M phi k delta c b profile theta atom matrix body profile'
    HP HM HA HB HE HProfile HProfileShift)
    as [theta' [atom' [matrix' [body' [HM' [HA' [HB' [HE' HProfile']]]]]]]].
  destruct (source_full_prv_wellformed M cb cc cn exB PEx) as [j [HBB HCB]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx matrixB exB j
    (or_intror eq_refl) HExB) HBB) as HMatrixBBound.
  assert (HBranch:context_bounded M ub uc un (succM M j)).
  { apply (proj2 (context_bounded_cons M sb sc cn matrixB ub uc un (succM M j) HCons)).
    split;[exact HMatrixBBound|]. exact (context_shift_preserves_bound M cb cc cn sb sc j HShift HCB). }
  assert (PProfile':source_full_prv M ub uc un profile').
  { apply (source_full_cons_weaken M sb sc cn matrixB ub uc un (succM M j) profile' HCons HBranch).
    exact (source_full_prv_renaming M cb cc cn profile (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) sb sc profile' PP HShift HProfileShift). }
  assert (RInput:numerical_renaming M input (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) input').
  { apply (proj2 (numerical_renaming_member M p b input (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) input' HInput)).
    exists (succM M p),(succM M b). split;[apply context_shift_lookup;reflexivity|].
    split;[apply context_shift_lookup;reflexivity|exact HInput']. }
  assert (PInput':source_full_prv M ub uc un input').
  { apply (source_full_cons_weaken M sb sc cn matrixB ub uc un (succM M j) input' HCons HBranch).
    exact (source_full_prv_renaming M cb cc cn input (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) sb sc input' PI HShift RInput). }
  pose proof (source_full_cons_head M sb sc cn matrixB ub uc un (succM M j)
    HCons HMatrixBBound HBranch) as PMatrixB.
  pose proof (source_full_conjunction_left M ub uc un bmem phixp matrixB HMatrixB PMatrixB) as PBMem.
  pose proof (source_full_conjunction_right M ub uc un bmem phixp matrixB HMatrixB PMatrixB) as PPhi.
  pose proof (source_full_trace_generic_member M ub uc un phi k (succM M delta)
    (succM M c) (succM M b) profile' theta' atom' matrix' body'
    (zeroM M) (succM M p) cmem bmem input' phixp rb rc
    HP HM' HA' HB' HE' HProfile' HCMem HBMem HInput' HMap HValue
    PProfile' PBMem PInput' PPhi) as PCMem.
  assert (PMatrixC:source_full_prv M ub uc un matrixC).
  { apply (full_source_CI M ub uc un cmem phixp matrixC);[|exact PCMem|exact PPhi|exact HMatrixC].
    exact (source_wf_binary M ub uc un SFAnd cmem phixp matrixC (or_introl eq_refl) HMatrixC
      (source_full_prv_wellformed M ub uc un cmem PCMem)
      (source_full_prv_wellformed M ub uc un phixp PPhi)). }
  destruct (numerical_renaming_total M exC (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1)) as [shifted HExShift].
  exact (source_full_exists_map M cb cc cn matrixB matrixC exB exC sb sc ub uc un shifted
    (source_trace_request_target_wf M cb cc cn c bmem cmem phixp matrixB matrixC exB exC
      HCMem HMatrixB HMatrixC HExB HExC PEx)
    HExB HExC HShift HCons HExShift PEx PMatrixC).
Qed.

Print Assumptions source_trace_request_target_wf.
Print Assumptions source_full_upper_trace_request_transfer.
