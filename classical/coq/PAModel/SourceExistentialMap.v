(** An actual existential witness-preserving source proof macro. The same
    variable0 witness is used to prove the target existential matrix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
  NumericalContextRenaming NumericalEnvironments NumericalContexts NumericalInstantiation
  SourceQuantifierRules SourceShiftSpecialization SourceSequents NumericalSourceFull
  SourceContextTransport SourceTraceBounds.
Unset Implicit Arguments.

Theorem source_shifted_exists_specialization M a ex shifted k :
  source_bounded M a k -> sf_relation M SFEx a (zeroM M) ex ->
  source_formula_shift M ex shifted ->
  exists ar,sf_relation M SFEx ar (zeroM M) shifted /\ numerical_instantiation M ar (zeroM M) a.
Proof.
  intros HA HEx HS.
  apply (proj1 (numerical_renaming_quantifier M false a ex (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) shifted HEx)) in HS.
  destruct HS as [rb [rc [rn [ar [HL [HR HOut]]]]]].
  exists ar. split;[exact HOut|].
  exact (source_lifted_shift_specialization M a k rb rc rn ar HA HL HR).
Qed.

Theorem source_full_exists_map M cb cc cn a b exa exb sb sc ub uc un shifted :
  source_sequent_wf M cb cc cn exb ->
  sf_relation M SFEx a (zeroM M) exa -> sf_relation M SFEx b (zeroM M) exb ->
  context_shift M cb cc cn sb sc -> environment_cons M sb sc cn a ub uc un ->
  source_formula_shift M exb shifted ->
  source_full_prv M cb cc cn exa -> source_full_prv M ub uc un b ->
  source_full_prv M cb cc cn exb.
Proof.
  intros HWF HA HB HC HCons HS PA PB.
  apply (full_source_ExE M cb cc cn a exa exb shifted sb sc ub uc un HWF PA);
    [|exact HA|exact HC|exact HCons|exact HS].
  destruct HWF as [k [HBound HCtx]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx b exb k (or_intror eq_refl) HB)
    HBound) as HBodyBound.
  destruct (source_shifted_exists_specialization M b exb shifted (succM M k)
    HBodyBound HB HS) as [br [HEx HInst]].
  apply (full_source_ExI M ub uc un br shifted (zeroM M) b).
  - assert (HShiftBound:source_bounded M shifted (succM M k)).
    { apply (numerical_renaming_preserves_bound M exb (zeroM M) (zeroM M) (zeroM M)
        (succM M (zeroM M)) shifted k (succM M k) HBound HS).
      intros i j HI HJ. apply context_shift_lookup in HJ. subst j.
      exact (proj2 (coding_lt_succ_cancel M i k) HI). }
    destruct (source_full_prv_wellformed M ub uc un b PB) as [j [_ HBranch]].
    apply (source_wf_transport_context M sb sc cn shifted ub uc un).
    + exists (succM M k). split;[exact HShiftBound|].
      exact (context_shift_preserves_bound M cb cc cn sb sc k HC HCtx).
    + now exists j.
  - exact PB.
  - exact HEx.
  - exact HInst.
Qed.

Print Assumptions source_shifted_exists_specialization.
Print Assumptions source_full_exists_map.
