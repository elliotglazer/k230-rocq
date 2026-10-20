(** The raw and WF-guarded Replacement ranges use the same input witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalSourceFull SourceQuantifierRules SourceTraceBounds SourceProofRenaming
  SourceProofWeakening SourceContextTransport SourceExistentialMap
  SourcePropositionalTemplates SourceWFReplacementBody.
Unset Implicit Arguments.

Definition wf_rep_env {A} (d d1 input theta:A) i :=
  match i with 0=>d|1=>d1|2=>input|_=>theta end.

Theorem source_full_wf_rep_exists_forward M b c n k domain domain1 input theta rawbody targetbody rawex targetex :
  (forall i,source_bounded M (wf_rep_env domain domain1 input theta i) (succM M k)) ->
  context_bounded M b c n k ->
  code_relation M (wf_rep_env domain domain1 input theta) (source_prop_expression wf_rep_raw_body) rawbody ->
  code_relation M (wf_rep_env domain domain1 input theta) (source_prop_expression wf_rep_target_body) targetbody ->
  sf_relation M SFEx rawbody (zeroM M) rawex ->sf_relation M SFEx targetbody (zeroM M) targetex ->
  source_full_prv M b c n rawex ->source_full_prv M b c n targetex.
Proof.
  intros HB HC HR HT HRaw HTarget PRaw.
  pose proof (source_prop_template_bound M _ wf_rep_raw_body (succM M k) HB rawbody HR) as HRawBound.
  pose proof (source_prop_template_bound M _ wf_rep_target_body (succM M k) HB targetbody HT) as HTargetBound.
  pose proof (proj2 (source_bounded_accept_unary M SFEx targetbody targetex k
    (or_intror eq_refl) HTarget) HTargetBound) as HE.
  destruct (context_shift_total M b c n) as [s [t HS]].
  destruct (environment_cons_total M s t n rawbody) as [u [v [l HCons]]].
  destruct (numerical_renaming_total M targetex (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [shifted HShift].
  apply (source_full_exists_map M b c n rawbody targetbody rawex targetex s t u v l shifted
    (ex_intro _ k (conj HE HC)) HRaw HTarget HS HCons HShift PRaw).
  assert (HBranch:context_bounded M u v l (succM M k)).
  { apply (proj2 (context_bounded_cons M s t n rawbody u v l _ HCons)).
    split;[exact HRawBound|exact (context_shift_preserves_bound M b c n s t k HS HC)]. }
  apply (source_full_wf_rep_body_forward M _ (succM M k) u v l rawbody targetbody HB HBranch HR HT).
  apply (full_source_Ctx M u v l rawbody).
  - exists (succM M k). now split.
  - apply (proj2 (context_member_cons M s t n rawbody u v l rawbody HCons)). now left.
Qed.

Theorem source_full_wf_rep_exists_reverse M b c n k domain domain1 input theta rawbody targetbody rawex targetex :
  (forall i,source_bounded M (wf_rep_env domain domain1 input theta i) (succM M k)) ->
  context_bounded M b c n k ->source_formula_shift M domain domain1 ->
  code_relation M (wf_rep_env domain domain1 input theta) (source_prop_expression wf_rep_raw_body) rawbody ->
  code_relation M (wf_rep_env domain domain1 input theta) (source_prop_expression wf_rep_target_body) targetbody ->
  sf_relation M SFEx rawbody (zeroM M) rawex ->sf_relation M SFEx targetbody (zeroM M) targetex ->
  source_full_prv M b c n domain ->source_full_prv M b c n targetex ->source_full_prv M b c n rawex.
Proof.
  intros HB HC HDShift HR HT HRaw HTarget PD PTarget.
  pose proof (source_prop_template_bound M _ wf_rep_raw_body (succM M k) HB rawbody HR) as HRawBound.
  pose proof (source_prop_template_bound M _ wf_rep_target_body (succM M k) HB targetbody HT) as HTargetBound.
  pose proof (proj2 (source_bounded_accept_unary M SFEx rawbody rawex k
    (or_intror eq_refl) HRaw) HRawBound) as HE.
  destruct (context_shift_total M b c n) as [s [t HS]].
  destruct (environment_cons_total M s t n targetbody) as [u [v [l HCons]]].
  destruct (numerical_renaming_total M rawex (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [shifted HShift].
  apply (source_full_exists_map M b c n targetbody rawbody targetex rawex s t u v l shifted
    (ex_intro _ k (conj HE HC)) HTarget HRaw HS HCons HShift PTarget).
  assert (HBranch:context_bounded M u v l (succM M k)).
  { apply (proj2 (context_bounded_cons M s t n targetbody u v l _ HCons)).
    split;[exact HTargetBound|exact (context_shift_preserves_bound M b c n s t k HS HC)]. }
  apply (source_full_wf_rep_body_reverse M _ (succM M k) u v l rawbody targetbody HB HBranch HR HT).
  - apply (full_source_Ctx M u v l targetbody).
    + exists (succM M k). now split.
    + apply (proj2 (context_member_cons M s t n targetbody u v l targetbody HCons)). now left.
  - change (source_full_prv M u v l domain1).
    apply (source_full_prv_weaken_bounded M s t n u v l domain1 (succM M k)
      (source_full_prv_renaming M b c n domain (zeroM M) (zeroM M) (zeroM M)
        (succM M (zeroM M)) s t domain1 PD HS HDShift));[|exact HBranch].
    intros f HF. apply (proj2 (context_member_cons M s t n targetbody u v l f HCons)). now right.
Qed.

Print Assumptions source_full_wf_rep_exists_forward.
Print Assumptions source_full_wf_rep_exists_reverse.
