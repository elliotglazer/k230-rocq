(** Preserve one chosen container while changing its defining predicate.
    Generalization is performed only after proving the marker and the
    entire raw-container assumption fresh in the tested element name. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments FreshNames QuotationPayloads SetFormulaCodes
  ContextualProofs ContextualDeduction ContextualPropositional ContextualLogic
  ContextualEquivalence StableContextSupport NumericalEquivalence NumericalVacuity
  NumericalVacuitySteps ProofTemplates ProofMacros NamedLeibnizSteps NamedExistential
  NumericalKP0.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem numerical_same_container_body M marker rawall domain rawbody point pointstep
    z tested_domain guarded allpoint targetbody result :
  quotation_binary M SFAnd domain rawall rawbody ->
  implication_graph M rawall point pointstep -> numerical_implies M marker pointstep ->
  formula_fresh M marker z -> formula_fresh M rawbody z ->
  implication_graph M tested_domain point guarded -> universal_graph M z guarded allpoint ->
  quotation_binary M SFAnd domain allpoint targetbody ->
  implication_graph M rawbody targetbody result -> numerical_implies M marker result.
Proof.
  intros HRaw HStep PStep HMfresh HRfresh HGuard HAll HTarget HResult.
  destruct (context_singleton_total M marker) as [mb [mc [mn HM]]].
  destruct (environment_cons_total M mb mc mn rawbody) as [rb [rc [rn HR]]].
  assert (SMarker : stable_context_support M rb rc rn marker).
  { apply (stable_context_support_cons M mb mc mn rawbody rb rc rn marker HR).
    apply stable_context_support_member.
    apply (proj2 (context_singleton_member M marker mb mc mn marker HM));reflexivity. }
  assert (PRaw : contextually_provable M rb rc rn rawbody).
  { apply contextual_hyp. apply (proj2 (context_member_cons M mb mc mn rawbody rb rc rn rawbody HR)).
    now left. }
  pose proof (contextual_conjunction_left M rb rc rn domain rawall rawbody HRaw PRaw) as PDomain.
  pose proof (contextual_conjunction_right M rb rc rn domain rawall rawbody HRaw PRaw) as PRawAll.
  pose proof (stable_context_support_here M rb rc rn pointstep
    (stable_context_support_implies M rb rc rn marker pointstep PStep SMarker)) as PImp.
  pose proof (contextual_mp M rb rc rn rawall point pointstep PRawAll PImp HStep) as PPoint.
  destruct (contextual_implication_intro M rb rc rn tested_domain point PPoint) as [guard [Hguard Pguard]].
  assert (guard=guarded) by exact (code_relation_functional M _ _ guard guarded Hguard HGuard).
  subst guard.
  assert (HFresh : context_fresh M rb rc rn z).
  { apply (proj2 (context_fresh_cons M mb mc mn rawbody rb rc rn z HR)).
    split;[exact HRfresh|]. intros f HF.
    apply (proj1 (context_singleton_member M marker mb mc mn f HM)) in HF.
    now subst f. }
  pose proof (contextual_gen M rb rc rn z guarded allpoint HFresh Pguard HAll) as PAll.
  pose proof (contextual_conjunction_intro M rb rc rn domain allpoint targetbody PDomain PAll HTarget) as PTarget.
  destruct (contextual_deduction M mb mc mn rawbody rb rc rn targetbody HR PTarget)
    as [actual [HActual PActual]].
  assert (actual=result) by exact (code_relation_functional M _ _ actual result HActual HResult).
  subst actual.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker mb mc mn result HM PActual) as [final [HFinal PFinal]].
  intros out HOut. assert (out=final) by exact (code_relation_functional M _ _ out final HOut HFinal).
  subst out. exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) final) PFinal).
Qed.

Theorem numerical_same_container_exists M marker container rawbody targetbody rawexists targetexists result bodyresult :
  formula_fresh M marker container ->
  implication_graph M rawbody targetbody bodyresult -> numerical_implies M marker bodyresult ->
  named_exists_graph M container rawbody rawexists ->
  named_exists_graph M container targetbody targetexists ->
  implication_graph M rawexists targetexists result -> numerical_implies M marker result.
Proof.
  intros HFresh HBody PBody HRaw HTarget HResult.
  set (env:=marker .: rawbody .: targetbody .: container .: fun _=>zeroM M).
  assert (HStep : ns_proof M env
    (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))).
  { destruct (code_relation_total M (E_wim (CEvar 1) (CEvar 2)) env) as [body EBody].
    assert (body=bodyresult).
    { exact (code_relation_functional M _ _ body bodyresult EBody HBody). }
    subst body. apply (proj2 (numerical_implies_expression M env (CEvar 0)
      (E_wim (CEvar 1) (CEvar 2)) marker bodyresult eq_refl EBody)). exact PBody. }
  assert (HVac : ns_proof M env (E_vac (CEvar 3) (CEvar 0))).
  { intros v EV. apply (numerical_vacuity M container marker v HFresh).
    exact (proj1 (expression_vacuity_graph M env (CEvar 3) (CEvar 0)
      container marker v eq_refl eq_refl) EV). }
  assert (HProgram : ns_proof M env
    (E_wim (CEvar 0) (E_wim (E_wex (CEvar 3) (CEvar 1)) (E_wex (CEvar 3) (CEvar 2))))).
  { apply (ns_proof_macro M env (E_vac (CEvar 3) (CEvar 0) ::
      E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) :: nil)).
    - intros e [<-|[<-|[]]];assumption.
    - apply kp0_parameter_exists;apply PM_input;cbn;tauto. }
  assert (ERaw : code_relation M env (E_wex (CEvar 3) (CEvar 1)) rawexists).
  { exact (proj2 (named_exists_expression M env (CEvar 3) (CEvar 1) container rawbody rawexists
      eq_refl eq_refl) HRaw). }
  assert (ETarget : code_relation M env (E_wex (CEvar 3) (CEvar 2)) targetexists).
  { exact (proj2 (named_exists_expression M env (CEvar 3) (CEvar 2) container targetbody targetexists
      eq_refl eq_refl) HTarget). }
  assert (EResult : code_relation M env
    (E_wim (E_wex (CEvar 3) (CEvar 1)) (E_wex (CEvar 3) (CEvar 2))) result).
  { exact (proj2 (expression_implication_iff M env (E_wex (CEvar 3) (CEvar 1))
      (E_wex (CEvar 3) (CEvar 2)) rawexists targetexists result ERaw ETarget) HResult). }
  exact (proj1 (numerical_implies_expression M env (CEvar 0)
    (E_wim (E_wex (CEvar 3) (CEvar 1)) (E_wex (CEvar 3) (CEvar 2))) marker result
    eq_refl EResult) HProgram).
Qed.

Print Assumptions numerical_same_container_body.
Print Assumptions numerical_same_container_exists.
