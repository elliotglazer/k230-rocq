(** The remaining axiom obligation for the lower consistency comparison.
    Logical proof preservation and actual marker/domain existence proofs
    discharge every other premise of this conditional transfer theorem. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent
  NumericalProofs NumericalEquivalence NumericalContexts NumericalEnvironments
  NumericalSourceFull SourceBounded FixedSourceBounds SourceInitialEnvironment
  NumericalQuotation QuotationHygiene QuotationBoundedEnvironment
  SupportedQuotationInvariant SupportedFullTranslation SupportedInitialContext ContextSupport
  ContextualProofs ContextualDeduction ContextualQuantifiers NamedExistential
  BootstrapSpecializations NumericalBootstrap NumericalVacuitySteps.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition marker_axiom_images M sb sc sn marker :=
  forall f q,context_member M sb sc sn f ->
    numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 4) (code_numeral M 1) q -> numerical_implies M marker q.

Theorem source_theory_contradiction_transfer M sb sc sn :
  context_bounded M sb sc sn (zeroM M) ->
  (forall marker,code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
    marker_axiom_images M sb sc sn marker) ->
  source_full_prv M sb sc sn (zeroM M) -> numerically_provable M (code_numeral M 1).
Proof.
  intros HClosed HA HSource.
  set (env:=fun _ : nat=>zeroM M).
  destruct (code_relation_total M specialized_marker_expression env) as [marker HMCode].
  destruct (code_relation_total M bootstrap_empty_expression env) as [empty HECode].
  assert (HE : named_exists_graph M (code_numeral M 1) marker empty).
  { exact (proj1 (named_exists_expression M env (CEconst 1) specialized_marker_expression
      (code_numeral M 1) marker empty eq_refl HMCode) HECode). }
  pose proof (numerical_empty_marker_exists M env empty HECode) as PE.
  pose proof (specialized_marker_fresh_three M env marker HMCode) as HFresh.
  destruct (specialized_member_exists M) as [dom [host [HD [HH PH]]]].
  pose proof (HA marker HMCode) as HImages.
  destruct (source_full_supported_quotation M sb sc sn (zeroM M) HSource) as [bound HT].
  destruct (constant_environment_total M bound (code_numeral M 3)) as [eb [ec HEnv]].
  assert (HSafe : quotation_safe M eb ec bound (code_numeral M 4) (code_numeral M 1)).
  { apply (constant_environment_safe M eb ec bound (code_numeral M 3)
      (code_numeral M 4) (code_numeral M 1) HEnv).
    - apply (proj2 (fixed_source_numeral_lt_iff M 3 4)). lia.
    - apply (proj2 (fixed_source_numeral_lt_iff M 0 4)). lia.
    - apply (proj2 (fixed_source_numeral_lt_iff M 1 4)). lia. }
  destruct (context_singleton_total M marker) as [mb [mc [mn HMarker]]].
  destruct (environment_cons_total M mb mc mn dom) as [db [dc [dn HDomain]]].
  assert (HM : context_support M db dc dn marker).
  { apply (context_support_cons M mb mc mn dom db dc dn marker HDomain).
    apply context_support_member. apply (proj2 (context_singleton_member M marker mb mc mn marker HMarker)).
    reflexivity. }
  assert (HDom : context_support M db dc dn dom).
  { apply context_support_member. apply (proj2 (context_member_cons M mb mc mn dom db dc dn dom HDomain)).
    now left. }
  assert (HAssumptions : quotation_assumptions_supported M sb sc sn eb ec bound
      (code_numeral M 4) (code_numeral M 1) db dc dn).
  { intros f q HF HQ.
    destruct (numerical_quotation_total M f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 4) (code_numeral M 1)) as [canonical HC].
    assert (canonical=q) by exact (numerical_quotation_closed_environment M f
      (zeroM M) (zeroM M) (zeroM M) eb ec bound (code_numeral M 4) (code_numeral M 1)
      canonical q (HClosed f HF) HC HQ).
    subst canonical. exact (context_support_implies M db dc dn marker q HM (HImages f q HF HC)). }
  assert (PF : contextually_provable M db dc dn (code_numeral M 1)).
  { apply (HT eb ec bound (code_numeral M 4) (code_numeral M 1) db dc dn
      (code_numeral M 1) (coding_lt_succ M bound) HSafe HAssumptions).
    - exact (quotation_constant_domains_supported M eb ec bound (code_numeral M 3)
        (code_numeral M 1) dom db dc dn HEnv HD HDom).
    - apply numerical_quotation_leaf. left. split;[now left|reflexivity]. }
  destruct (contextual_deduction M mb mc mn dom db dc dn (code_numeral M 1) HDomain PF)
    as [df [HDF PDF]].
  assert (HF : contextually_provable M mb mc mn (code_numeral M 1)).
  { apply (contextual_exists_elimination M mb mc mn (code_numeral M 3) dom
      (code_numeral M 1) host df).
    - intros f Hf. apply (proj1 (context_singleton_member M marker mb mc mn f HMarker)) in Hf.
      now subst f.
    - apply bootstrap_false_fresh_three.
    - exact HH.
    - exact HDF.
    - now apply contextual_global.
    - exact PDF. }
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M) marker mb mc mn
    (code_numeral M 1) HMarker HF) as [mf [HMF PMF]].
  apply (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) (code_numeral M 1))).
  apply (contextual_exists_elimination M (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1) marker (code_numeral M 1) empty mf).
  - intros f Hf. exfalso. exact (context_empty M (zeroM M) (zeroM M) f Hf).
  - apply bootstrap_false_fresh_one.
  - exact HE.
  - exact HMF.
  - now apply contextual_global.
  - exact PMF.
Qed.

Print Assumptions source_theory_contradiction_transfer.
