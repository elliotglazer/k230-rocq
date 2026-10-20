(** Initialize the supported quotation invariant. Source hypotheses must
    already have actual internal K proofs of their quotations. All live
    entries of a constant environment use a single domain assumption. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeDescent CodeTags
  NumericalProofs NumericalContexts NumericalEnvironments NumericalQuotation
  SourceSequents SourceInitialEnvironment QuotationHygiene ContextSupport
  ContextualProofs ContextualDeduction SupportedQuotationInvariant.
Unset Implicit Arguments.

Theorem quotation_assumptions_supported_global M sb sc sn eb ec en fresh domain tb tc tn :
  (forall f q, context_member M sb sc sn f ->
    numerical_quotation M f eb ec en fresh domain q -> numerically_provable M q) ->
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn.
Proof. intros HP f q HF HQ. left. exact (HP f q HF HQ). Qed.

Theorem quotation_constant_domains_supported M eb ec en x domain dom tb tc tn :
  constant_environment M eb ec en x -> membership_graph M domain x dom ->
  context_support M tb tc tn dom ->
  quotation_domains_supported M eb ec en domain tb tc tn.
Proof.
  intros HE HD HP i y d Hi HY Hd.
  pose proof (constant_environment_lookup M eb ec en x i y HE Hi HY) as Ey.
  subst y. assert (Ed : d=dom) by exact (tagged_pair_functional M 1 domain x d dom Hd HD).
  now subst d.
Qed.

Theorem quotation_constant_singleton_domains M eb ec en x domain dom tb tc tn :
  constant_environment M eb ec en x -> membership_graph M domain x dom ->
  context_singleton M dom tb tc tn ->
  quotation_domains_supported M eb ec en domain tb tc tn.
Proof.
  intros HE HD HT. apply (quotation_constant_domains_supported M eb ec en x domain dom tb tc tn HE HD).
  apply context_support_member.
  apply (proj2 (context_singleton_member M dom tb tc tn dom HT)). reflexivity.
Qed.

Theorem supported_initial_environment_total M bound :
  exists eb ec dom tb tc tn,
    constant_environment M eb ec bound (succM M (zeroM M)) /\
    quotation_safe M eb ec bound (succM M (succM M (zeroM M))) (zeroM M) /\
    membership_graph M (zeroM M) (succM M (zeroM M)) dom /\
    context_singleton M dom tb tc tn /\
    quotation_domains_supported M eb ec bound (zeroM M) tb tc tn.
Proof.
  destruct (constant_environment_total M bound (succM M (zeroM M))) as [eb [ec HE]].
  destruct (tagged_pair_total M 1 (zeroM M) (succM M (zeroM M))) as [dom HD].
  destruct (context_singleton_total M dom) as [tb [tc [tn HT]]].
  exists eb,ec,dom,tb,tc,tn. split;[exact HE|]. split.
  - apply (constant_environment_safe M eb ec bound (succM M (zeroM M))
      (succM M (succM M (zeroM M))) (zeroM M) HE).
    + apply coding_lt_succ.
    + apply coding_zero_lt_succ.
    + apply coding_zero_lt_succ.
  - split;[exact HD|]. split;[exact HT|].
    exact (quotation_constant_singleton_domains M eb ec bound (succM M (zeroM M))
      (zeroM M) dom tb tc tn HE HD HT).
Qed.

Theorem source_supported_initial_context M bound r sb sc sn f
    eb ec x fresh domain dom tb tc tn q :
  source_supported_good M bound r -> source_sequent M sb sc sn f r ->
  constant_environment M eb ec bound x ->
  coding_lt M x fresh -> coding_lt M (zeroM M) fresh -> coding_lt M domain fresh ->
  membership_graph M domain x dom -> context_singleton M dom tb tc tn ->
  (forall h p, context_member M sb sc sn h ->
    numerical_quotation M h eb ec bound fresh domain p -> numerically_provable M p) ->
  numerical_quotation M f eb ec bound fresh domain q ->
  contextually_provable M tb tc tn q.
Proof.
  intros HG Hr HE HX HZ HD Hdom HT HSource HQ.
  exact (proj1 (proj2 HG) sb sc sn f Hr eb ec bound fresh domain tb tc tn q
    (coding_lt_succ M bound)
    (constant_environment_safe M eb ec bound x fresh domain HE HX HZ HD)
    (quotation_assumptions_supported_global M sb sc sn eb ec bound fresh domain tb tc tn HSource)
    (quotation_constant_singleton_domains M eb ec bound x domain dom tb tc tn HE Hdom HT) HQ).
Qed.

Theorem source_supported_initial_implication M bound r sb sc sn f
    eb ec x fresh domain dom tb tc tn q :
  source_supported_good M bound r -> source_sequent M sb sc sn f r ->
  constant_environment M eb ec bound x ->
  coding_lt M x fresh -> coding_lt M (zeroM M) fresh -> coding_lt M domain fresh ->
  membership_graph M domain x dom -> context_singleton M dom tb tc tn ->
  (forall h p, context_member M sb sc sn h ->
    numerical_quotation M h eb ec bound fresh domain p -> numerically_provable M p) ->
  numerical_quotation M f eb ec bound fresh domain q ->
  exists implication, implication_graph M dom q implication /\ numerically_provable M implication.
Proof.
  intros HG Hr HE HX HZ HD Hdom HT HSource HQ.
  pose proof (source_supported_initial_context M bound r sb sc sn f
    eb ec x fresh domain dom tb tc tn q HG Hr HE HX HZ HD Hdom HT HSource HQ) as HP.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    dom tb tc tn q HT HP) as [imp [HI PI]].
  exists imp. split;[exact HI|].
  exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) imp) PI).
Qed.

Print Assumptions supported_initial_environment_total.
Print Assumptions source_supported_initial_context.
Print Assumptions source_supported_initial_implication.
