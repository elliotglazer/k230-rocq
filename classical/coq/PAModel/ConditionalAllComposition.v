(** Compose two numerical implications under a marker, then close the
    domain variable. Only global implications are transported into the
    extra context; no unrestricted contextual weakening is used. *)
From PAModel Require Import Model CodeExpressions NumericalProofs NumericalEquivalence
  NumericalContexts NumericalEnvironments FreshNames ContextualProofs ContextualDeduction
  StableContextSupport.
Unset Implicit Arguments.

Theorem numerical_conditional_all_composition M marker domain raw target rawstep transfer step a result :
  implication_graph M domain raw rawstep -> numerical_implies M marker rawstep ->
  implication_graph M raw target transfer -> numerical_implies M marker transfer ->
  implication_graph M domain target step -> universal_graph M a step result ->
  formula_fresh M marker a -> numerical_implies M marker result.
Proof.
  intros HRaw PRaw HTransfer PTransfer HStep HAll HFresh.
  destruct (context_singleton_total M marker) as [mb [mc [mn HM]]].
  destruct (environment_cons_total M mb mc mn domain) as [db [dc [dn HD]]].
  assert (SMarker : stable_context_support M db dc dn marker).
  { apply (stable_context_support_cons M mb mc mn domain db dc dn marker HD).
    apply stable_context_support_member.
    apply (proj2 (context_singleton_member M marker mb mc mn marker HM));reflexivity. }
  assert (PDomain : contextually_provable M db dc dn domain).
  { apply contextual_hyp. apply (proj2 (context_member_cons M mb mc mn domain db dc dn domain HD)). now left. }
  pose proof (stable_context_support_here M db dc dn rawstep
    (stable_context_support_implies M db dc dn marker rawstep PRaw SMarker)) as PR.
  pose proof (stable_context_support_here M db dc dn transfer
    (stable_context_support_implies M db dc dn marker transfer PTransfer SMarker)) as PT.
  pose proof (contextual_mp M db dc dn domain raw rawstep PDomain PR HRaw) as PSelected.
  pose proof (contextual_mp M db dc dn raw target transfer PSelected PT HTransfer) as PTarget.
  destruct (contextual_deduction M mb mc mn domain db dc dn target HD PTarget)
    as [actual [HActual PActual]].
  assert (actual=step) by exact (code_relation_functional M _ _ actual step HActual HStep).
  subst actual.
  assert (HCtxFresh : context_fresh M mb mc mn a).
  { intros h HH. apply (proj1 (context_singleton_member M marker mb mc mn h HM)) in HH. now subst h. }
  pose proof (contextual_gen M mb mc mn a step result HCtxFresh PActual HAll) as PAll.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker mb mc mn result HM PAll) as [final [HFinal PFinal]].
  intros out HOut. assert (out=final) by exact (code_relation_functional M _ _ out final HOut HFinal).
  subst out. exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) final) PFinal).
Qed.

Print Assumptions numerical_conditional_all_composition.
