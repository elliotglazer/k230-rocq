(** Exact arithmetic constructor alignment for uniform WF Replacement.
    All formula, matrix, context and bound codes may be nonstandard. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions ProofTemplates
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceBoundMonotone
  NumericalContexts NumericalEnvironments NumericalSourceFull SourceProofWeakening SourceTraceBounds
  SourceRelativizationBounds SourceDomainInstances SourceQuantifierRules
  QuotationSchemaSkeleton SourceSchemaRelativization SourceRelativeSchemaConstructors
  SourceRelativeSchemaInputs SchemaRenamingDescriptors SourceReplacementGuardRenaming
  SourceFunctionalityShells SourceReplacementFunctionality SourcePropositionalRebase
  SourceWFSeparationConstructor SourceWFFormula NumericalWFFoundation WFClosureFiniteBridge
  SourceWFReplacementProfiles SourceWFReplacementOpen SourceDerivedRules.
Unset Implicit Arguments.

Lemma source_replacement_functionality_rebase M ma mb mc f :
  code_relation M (schema_env3 ma mb mc) (E_sf_functionality (CEvar 0) (CEvar 1)) f ->
  source_functionality_graph M ma mb f.
Proof.
  intro H.
  assert (HH:forall i,code_relation M (schema_env3 ma mb mc)
    (match i with 0=>CEvar 0|1=>CEvar 1|_=>CEconst 0 end)
    (schema_env3 ma mb (zeroM M) i)).
  { intros [|[|i]];reflexivity. }
  exact (proj1 (code_subst_graph M _ _ _ HH
    (E_sf_functionality (CEvar 0) (CEvar 1)) f) H).
Qed.

Lemma source_replacement_relative_functionality_rebase M d ra rb rc f :
  code_relation M (skeleton_relative_environment d (schema_env3 ra rb rc))
    (E_sf_relative_functionality (CEvar 0) (CEvar 1) (CEvar 2)) f ->
  source_relative_functionality_graph M d ra rb f.
Proof.
  intro H.
  assert (HH:forall i,code_relation M (skeleton_relative_environment d (schema_env3 ra rb rc))
    (schema_env3 (CEvar 0) (CEvar 1) (CEvar 2) i) (schema_env3 d ra rb i)).
  { intros [|[|i]];reflexivity. }
  exact (proj1 (code_subst_graph M _ _ _ HH
    (E_sf_relative_functionality (CEvar 0) (CEvar 1) (CEvar 2)) f) H).
Qed.

Definition E_replacement_raw_profile theta :=
  E_sf_all (E_sf_iff (E_sf_mem 0 1)
    (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3) theta))).

Local Opaque source_wf_domain_code source_wf_domain1_code source_wf_closure_code.

Lemma source_WF_replacement_raw_profile_rebase M ma mb mc rc guards profile :
  sf_relation M SFAnd (source_wf_domain_code M) (source_wf_domain1_code M) guards ->
  sf_relation M SFAnd guards rc mc ->
  code_relation M (schema_env3 ma mb mc) (E_replacement_raw_profile (CEvar 2)) profile ->
  source_wf_rep_raw_profile_graph M rc profile.
Proof.
  intros HG HC HP.
  assert (HOld:forall i:nat,code_relation M (schema_env3 ma mb mc) (CEvar 2) ((fun _:nat=>mc) i)).
  { intro i. reflexivity. }
  pose proof (proj1 (code_subst_graph M (schema_env3 ma mb mc) (fun _=>CEvar 2)
    (fun _=>mc) HOld (E_replacement_raw_profile (CEvar 0)) profile) HP) as H.
  assert (HNew:forall i:nat,code_relation M (wf_rep_profile_env M rc)
    (E_sf SFAnd (E_sf SFAnd (CEvar 0) (CEvar 1)) (CEvar 2)) ((fun _=>mc) i)).
  { intro i. functionality_graph. }
  exact (proj2 (code_subst_graph M (wf_rep_profile_env M rc)
    (fun _=>E_sf SFAnd (E_sf SFAnd (CEvar 0) (CEvar 1)) (CEvar 2))
    (fun _=>mc) HNew (E_replacement_raw_profile (CEvar 0)) profile) H).
Qed.

Lemma source_WF_replacement_target_profile_rebase M ra rb rc profile :
  code_relation M (skeleton_relative_environment (source_wf_domain_code M) (schema_env3 ra rb rc))
    (E_wf_rep_target_profile (CEvar 0) (CEvar 3)) profile ->
  source_wf_rep_target_profile_graph M rc profile.
Proof.
  intro HP.
  set (values:=fun i:nat=>match i with 0=>source_wf_domain_code M|_=>rc end).
  assert (HOld:forall i,code_relation M
    (skeleton_relative_environment (source_wf_domain_code M) (schema_env3 ra rb rc))
    (match i with 0=>CEvar 0|_=>CEvar 3 end) (values i)).
  { intros [|i];reflexivity. }
  pose proof (proj1 (code_subst_graph M _ _ values HOld
    (E_wf_rep_target_profile (CEvar 0) (CEvar 1)) profile) HP) as H.
  assert (HNew:forall i,code_relation M (wf_rep_profile_env M rc)
    (match i with 0=>CEvar 0|_=>CEvar 2 end) (values i)).
  { intros [|i];reflexivity. }
  exact (proj2 (code_subst_graph M _ _ values HNew
    (E_wf_rep_target_profile (CEvar 0) (CEvar 1)) profile) H).
Qed.

Ltac wf_replacement_expression_bound :=
  lazymatch goal with
  | |- schema_expression_bound _ _ (CEvar _) _ =>
      apply schema_expression_variable;cbn [skeleton_relative_environment schema_env3];
        first [assumption|apply sr_domain_bound_succ;exact (numerical_wf_domain_bounded _)]
  | |- schema_expression_bound _ _ (E_sf_iff _ _) _ =>
      apply schema_expression_iff;wf_replacement_expression_bound
  | |- schema_expression_bound _ _ (E_sf SFAll _ _) _ =>
      apply schema_expression_unary;[now left|wf_replacement_expression_bound]
  | |- schema_expression_bound _ _ (E_sf SFEx _ _) _ =>
      apply schema_expression_unary;[now right|wf_replacement_expression_bound]
  | |- schema_expression_bound _ _ (E_sf SFMember _ _) _ =>
      apply schema_expression_atom;[now left|schema_small_index|schema_small_index]
  | |- schema_expression_bound _ _ (E_sf SFEqual _ _) _ =>
      apply schema_expression_atom;[now right|schema_small_index|schema_small_index]
  | |- schema_expression_bound _ _ (E_sf SFAnd _ _) _ =>
      apply schema_expression_binary;[now left|wf_replacement_expression_bound|wf_replacement_expression_bound]
  | |- schema_expression_bound _ _ (E_sf SFImpl _ _) _ =>
      apply schema_expression_binary;[now right;right|wf_replacement_expression_bound|wf_replacement_expression_bound]
  end.

Lemma source_WF_relative_replacement_bound M ra rb rc target n :
  source_bounded M ra (succM M (succM M (succM M n))) ->
  source_bounded M rb (succM M (succM M (succM M n))) ->
  source_bounded M rc (succM M (succM M (succM M (succM M n)))) ->
  sf_relative_replacement_constructor M (source_wf_domain_code M) ra rb rc target ->
  source_bounded M target n.
Proof.
  intros HA HB HC HF. unfold sf_relative_replacement_constructor in HF.
  rewrite relative_replacement_skeleton_exact in HF.
  assert (HBound:schema_expression_bound M
    (skeleton_relative_environment (source_wf_domain_code M) (schema_env3 ra rb rc))
    (E_sf_relative_replacement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) n).
  { unfold E_sf_relative_replacement,E_sf_relative_functionality,E_sf_relative_all,
      E_sf_relative_ex,E_sf_all,E_sf_ex,E_sf_mem,E_sf_eq.
    wf_replacement_expression_bound. }
  exact (HBound target HF).
Qed.

Theorem source_full_WF_replacement_open M b c l n rphi matrix ra rb rc ma mb mc raw target :
  context_bounded M b c l (zeroM M) ->
  source_bounded M ra (succM M (succM M (succM M n))) ->
  source_bounded M rb (succM M (succM M (succM M n))) ->
  source_bounded M rc (succM M (succM M (succM M (succM M n)))) ->
  relative_replacement_matrix M (source_wf_domain_code M) rphi matrix ->
  schema_renaming M RepA matrix ma ->schema_renaming M RepB matrix mb ->schema_renaming M RepC matrix mc ->
  schema_renaming M RepA rphi ra ->schema_renaming M RepB rphi rb ->schema_renaming M RepC rphi rc ->
  sf_replacement_constructor M ma mb mc raw ->
  sf_relative_replacement_constructor M (source_wf_domain_code M) ra rb rc target ->
  source_full_prv M b c l (source_wf_closure_code M) ->source_full_prv M b c l raw ->
  source_full_prv M b c l target.
Proof.
  intros HClosed HA HB HC HM HMA HMB HMC HRA HRB HRC HRaw HTarget PC PR.
  pose proof (source_WF_relative_replacement_bound M ra rb rc target n HA HB HC HTarget) as HBound.
  unfold sf_replacement_constructor,E_sf_replacement in HRaw.
  destruct (schema_expression_split M _ SFImpl _ _ raw HRaw)
    as [nf [rawrhs [HNF [HRawRHS HRawImpl]]]].
  pose proof (source_replacement_functionality_rebase M ma mb mc nf HNF) as HNF'.
  destruct (schema_expression_quantifier_split M _ SFAll _ rawrhs HRawRHS)
    as [rawex [HRawEx HRawAll]].
  destruct (schema_expression_quantifier_split M _ SFEx _ rawex HRawEx)
    as [rawprofile [HRawProfile HRawExists]].
  pose proof (source_domain_instance_zero M (source_wf_domain_code M) (numerical_wf_domain_bounded M)) as HD0.
  pose proof (source_domain_instance_shift M (source_wf_domain_code M) (zeroM M)
    (source_wf_domain_code M) (source_wf_domain1_code M)
    (numerical_wf_domain_bounded M) HD0 (source_wf_domain1_shift M)) as HD1.
  destruct (source_guarded_matrix_schema_renaming M RepC (source_wf_domain_code M)
    rphi matrix rc mc (source_wf_domain_code M) (source_wf_domain1_code M)
    (numerical_wf_domain_bounded M) HM HMC HRC HD0 HD1) as [guards [HG HCGuard]].
  pose proof (source_WF_replacement_raw_profile_rebase M ma mb mc rc guards rawprofile
    HG HCGuard HRawProfile) as HRawProfile'.
  unfold sf_relative_replacement_constructor in HTarget.
  rewrite relative_replacement_skeleton_exact in HTarget.
  unfold E_sf_relative_replacement in HTarget.
  destruct (schema_expression_split M _ SFImpl _ _ target HTarget)
    as [rf [rhs [HRF [HRHS HTargetImpl]]]].
  pose proof (source_replacement_relative_functionality_rebase M _ ra rb rc rf HRF) as HRF'.
  cbn [E_sf_relative_all E_sf_relative_ex E_sf_all E_sf_ex] in HRHS.
  destruct (schema_expression_quantifier_split M _ SFAll _ rhs HRHS)
    as [outerguard [HOuterGuard HAll]].
  destruct (schema_expression_split M _ SFImpl _ _ outerguard HOuterGuard)
    as [d [targetex [HD [HTargetEx HOuter]]]].
  change (d=source_wf_domain_code M) in HD. subst d.
  destruct (schema_expression_quantifier_split M _ SFEx _ targetex HTargetEx)
    as [witness [HWitness HExists]].
  destruct (schema_expression_split M _ SFAnd _ _ witness HWitness)
    as [d [targetprofile [HD [HTargetProfile HWitnessAnd]]]].
  change (d=source_wf_domain_code M) in HD. subst d.
  pose proof (source_WF_replacement_target_profile_rebase M ra rb rc targetprofile HTargetProfile) as HTargetProfile'.
  destruct (proj1 (source_bounded_accept_binary M SFImpl rf rhs target n
    (or_intror (or_intror eq_refl)) HTargetImpl) HBound) as [HRFBound HRHSBound].
  assert (HCtx:context_bounded M b c l n).
  { exact (context_bounded_monotone M b c l (zeroM M) n HClosed (coding_zero_lt_succ M n)). }
  destruct (environment_cons_total M b c l rf) as [u [v [j HCons]]].
  assert (HBranch:context_bounded M u v j n).
  { exact (proj2 (context_bounded_cons M b c l rf u v j n HCons) (conj HRFBound HCtx)). }
  assert (HI:context_included M b c l u v j).
  { intros a HIn. apply (proj2 (context_member_cons M b c l rf u v j a HCons)). now right. }
  assert (PRF:source_full_prv M u v j rf).
  { apply full_source_Ctx;[exists n;auto|].
    apply (proj2 (context_member_cons M b c l rf u v j rf HCons)). now left. }
  pose proof (source_full_guarded_replacement_functionality M u v j n (source_wf_domain_code M)
    rphi matrix ra rb ma mb rf nf HBranch (numerical_wf_domain_bounded M) HA HB
    HM HMA HMB HRA HRB HRF' HNF' PRF) as PNF.
  pose proof (source_full_prv_weaken_bounded M b c l u v j raw n PR HI HBranch) as PRaw.
  pose proof (source_full_modus_ponens M u v j nf rawrhs raw HRawImpl PRaw PNF) as PRHS.
  pose proof (source_full_prv_weaken_bounded M b c l u v j (source_wf_closure_code M) n PC HI HBranch) as PClosure.
  pose proof (source_full_WF_replacement_rhs_graphs M u v j n rc rawprofile rawex rawrhs
    targetprofile witness targetex outerguard rhs HBranch HC HRawProfile' HTargetProfile'
    HRawExists HRawAll HWitnessAnd HExists HOuter HAll HRHSBound PClosure PRHS) as PResult.
  exact (full_source_II M b c l rf rhs target u v j
    (ex_intro _ n (conj HBound HCtx)) PResult HCons HTargetImpl).
Qed.

Print Assumptions source_replacement_functionality_rebase.
Print Assumptions source_replacement_relative_functionality_rebase.
Print Assumptions source_WF_replacement_raw_profile_rebase.
Print Assumptions source_WF_replacement_target_profile_rebase.
Print Assumptions source_WF_relative_replacement_bound.
Print Assumptions source_full_WF_replacement_open.
