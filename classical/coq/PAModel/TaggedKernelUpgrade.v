(** Upgrade the same constructed container from upper containment and
    universal requests to an exact tagged profile. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps FreshNames NamedBinderFresh TemplateBinderFresh TemplateFormulaFresh
  NumericalVacuitySteps NumericalSingleton NumericalRawPair NumericalTaggedComprehension
  NumericalTaggedKernel TaggedLowerClosure TaggedSelectedAllocation
  TaggedUniversalSelected RawMarkerExclusions RawMarkerQuantifiers
  NumericalKP0 NumericalKP0Eligibility NumericalBootstrap TemplatePropositional ProofMacros QuantifierMacros QuotientAtomTemplates.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition E_tagged_exact y carrier marker container theta :=
  E_wal y (E_wa
    (E_wim (E_wel y container) (E_tagged_profile y carrier marker theta))
    (E_wim (E_tagged_profile y carrier marker theta) (E_wel y container))).
Definition E_tagged_upgrade_antecedent :=
  E_wa (E_marker_empty (CEvar 4) (CEvar 7))
    (E_wa (E_wn (E_weq (CEvar 3) (CEvar 4)))
      (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))).
Definition E_tagged_upgrade_payload :=
  E_wa (E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7))
    (E_tagged_containment (CEvar 0) (CEvar 3) (CEvar 4) (CEvar 6) (CEvar 8)).
Definition E_tagged_upgrade_exact :=
  E_tagged_exact (CEvar 0) (CEvar 3) (CEvar 4) (CEvar 6) (CEvar 8).

Lemma tagged_all_conjunction y a b :
  proof_macro nil nil (E_wim (E_wal y a) (E_wim (E_wal y b) (E_wal y (E_wa a b)))).
Proof.
  assert (H:proof_macro nil nil
    (E_wim (E_wal y a) (E_wal y (E_wim b (E_wa a b))))).
  { apply macro_all_monotone,PM_template,kp0_conjunction. }
  apply macro_discharge. do 2 apply macro_deduction.
  eapply md_mp with (a:=E_wal y b);[apply md_hyp;now left|].
  eapply md_mp with (a:=E_wal y (E_wim b (E_wa a b))).
  - eapply md_mp with (a:=E_wal y a);[apply md_hyp;now right;left|].
    apply md_global,H.
  - apply md_global,PM_template,template_r2.
Qed.

Theorem numerical_tagged_kernel_upgrade M rho :
  selected_fixed_roles_distinct M rho -> selected_fixed_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) ->
  named_binder_absent M (rho 8) (rho 5) -> named_binder_absent M (rho 8) (rho 4) ->
  ns_proof M rho (E_wim E_tagged_upgrade_antecedent
    (E_wim E_tagged_upgrade_payload E_tagged_upgrade_exact)).
Proof.
  intros HD HN HF HR HT.
  set (Req:=E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7)).
  set (Upper:=E_tagged_containment (CEvar 0) (CEvar 3) (CEvar 4) (CEvar 6) (CEvar 8)).
  set (Lower:=E_wal (CEvar 0) (E_tagged_lower_body (CEvar 0) (CEvar 8))).
  apply (ns_proof_macro M rho
    (E_wim E_tagged_lower_context Lower :: E_wim Upper (E_wim Lower E_tagged_upgrade_exact) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_tagged_lower_closed M rho HD HN HF HR HT).
    + apply ns_proof_macro with (inputs:=nil);[intros e []|]. apply tagged_all_conjunction.
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=Lower).
    + eapply md_mp with (a:=E_tagged_lower_context).
      * unfold E_tagged_lower_context. apply kp0_md_conjunction.
        -- apply tagged_md_left with
            (b:=E_wa (E_wn (E_weq (CEvar 3) (CEvar 4)))
              (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))),md_hyp;now right;left.
        -- apply kp0_md_conjunction.
           ++ apply tagged_md_left with (b:=E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7)),
                tagged_md_right with (a:=E_marker_empty (CEvar 4) (CEvar 7)),md_hyp;now right;left.
           ++ apply kp0_md_conjunction.
              ** apply tagged_md_right with (a:=E_wn (E_weq (CEvar 3) (CEvar 4))),
                   tagged_md_right with (a:=E_marker_empty (CEvar 4) (CEvar 7)),md_hyp;now right;left.
              ** apply tagged_md_left with (b:=Upper),md_hyp;now left.
      * apply md_global,PM_input;now left.
    + eapply md_mp with (a:=Upper).
      * apply tagged_md_right with (a:=Req),md_hyp;now left.
      * apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_tagged_kernel_lift M rho :
  selected_fixed_roles_distinct M rho -> selected_fixed_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) ->
  named_binder_absent M (rho 8) (rho 5) -> named_binder_absent M (rho 8) (rho 4) ->
  ns_proof M rho (E_wim E_tagged_upgrade_antecedent
    (E_wim (E_wex (CEvar 6) E_tagged_upgrade_payload)
      (E_wex (CEvar 6) E_tagged_upgrade_exact))).
Proof.
  intros HD HN HF HR HT.
  assert (HV:ns_proof M rho (E_vac (CEvar 6) E_tagged_upgrade_antecedent)).
  { apply (kp0_expression_fresh_vacuity M rho (CEvar 6) E_tagged_upgrade_antecedent (rho 6) eq_refl).
    unfold E_tagged_upgrade_antecedent. apply expression_fresh_conjunction.
    - exact (HN 6 ltac:(lia) ltac:(lia)).
    - apply (marker_empty_fresh M rho (CEvar 4) (CEvar 7) (rho 4) (rho 7) (rho 6)
        eq_refl eq_refl (HN 6 ltac:(lia) ltac:(lia))
        (HD 4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 7 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    - apply expression_fresh_conjunction;[exact (HN 6 ltac:(lia) ltac:(lia))| |].
      + apply expression_fresh_negation;[exact (HN 6 ltac:(lia) ltac:(lia))|].
        apply expression_fresh_atom;[now right| |].
        * exact (marker_name_avoids M rho (CEvar 3) (rho 3) (rho 6) eq_refl
            (HD 3 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        * exact (marker_name_avoids M rho (CEvar 4) (rho 4) (rho 6) eq_refl
            (HD 4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      + exact (marker_pair_fresh M rho (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7)
          (rho 3) (rho 4) (rho 5) (rho 7) (rho 6) eq_refl eq_refl eq_refl eq_refl
          (HN 6 ltac:(lia) ltac:(lia))
          (HD 3 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          (HD 4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          (HD 5 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          (HD 7 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
  apply (ns_proof_macro M rho
    (E_vac (CEvar 6) E_tagged_upgrade_antecedent ::
     E_wim E_tagged_upgrade_antecedent (E_wim E_tagged_upgrade_payload E_tagged_upgrade_exact) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact HV.
    + exact (numerical_tagged_kernel_upgrade M rho HD HN HF HR HT).
  - apply kp0_parameter_exists;apply PM_input;cbn;tauto.
Qed.

Print Assumptions numerical_tagged_kernel_upgrade.
Print Assumptions numerical_tagged_kernel_lift.
