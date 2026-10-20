(** Context operations for the full source quotation invariant. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments NumericalQuotation QuotationFunctionality
  ContextSupport SupportedQuotationInvariant SourceSequents SourceTraceBounds SourceBounded
  ContextualProofs NumericalEquivalence QuotationHygiene QuotationRebase.
Unset Implicit Arguments.

Lemma source_row_bound_sequent M r bound b c n f :
  source_row_at_bound M r bound -> source_sequent M b c n f r ->
  source_bounded M f bound /\ context_bounded M b c n bound.
Proof.
  intros [[b' [c' [n' [f' [Hr [HF HC]]]]]]|[b' [c' [n' [a [d [f' [Hr H]]]]]]]] HS.
  - destruct (source_sequent_injective M b' c' n' f' b c n f r Hr HS)
      as [-> [-> [-> ->]]]. auto.
  - exfalso. exact (source_row_kinds_disjoint M b c n f b' c' n' a d f' r HS Hr).
Qed.
Lemma source_row_bound_branches M r bound b c n a d f :
  source_row_at_bound M r bound -> source_branches M b c n a d f r ->
  source_bounded M a bound /\ source_bounded M d bound /\
  source_bounded M f bound /\ context_bounded M b c n bound.
Proof.
  intros [[b' [c' [n' [f' [Hr H]]]]]|[b' [c' [n' [a' [d' [f' [Hr H]]]]]]]] HS.
  - exfalso. exact (source_row_kinds_disjoint M b' c' n' f' b c n a d f r Hr HS).
  - destruct (source_branches_injective M b' c' n' a' d' f' b c n a d f r Hr HS)
      as [-> [-> [-> [-> [-> ->]]]]]. exact H.
Qed.

Lemma quotation_assumptions_supported_target_cons M sb sc sn eb ec en fresh domain
    tb tc tn h td te tm :
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
  environment_cons M tb tc tn h td te tm ->
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain td te tm.
Proof.
  intros HC HT f q HF HQ. apply (context_support_cons M tb tc tn h td te tm q HT).
  exact (HC f q HF HQ).
Qed.
Lemma quotation_domains_supported_target_cons M eb ec en domain tb tc tn h td te tm :
  quotation_domains_supported M eb ec en domain tb tc tn ->
  environment_cons M tb tc tn h td te tm ->
  quotation_domains_supported M eb ec en domain td te tm.
Proof.
  intros HD HT i y d Hi HY Hd. apply (context_support_cons M tb tc tn h td te tm d HT).
  exact (HD i y d Hi HY Hd).
Qed.
Lemma quotation_assumptions_supported_cons M sb sc sn a su sv sl
    eb ec en fresh domain tb tc tn qa td te tm :
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
  numerical_quotation M a eb ec en fresh domain qa ->
  environment_cons M sb sc sn a su sv sl -> environment_cons M tb tc tn qa td te tm ->
  quotation_assumptions_supported M su sv sl eb ec en fresh domain td te tm.
Proof.
  intros HC HA HSource HTarget f q HF HQ.
  apply (proj1 (context_member_cons M sb sc sn a su sv sl f HSource)) in HF.
  destruct HF as [->|HF].
  - assert (q=qa) by exact (numerical_quotation_functional M a eb ec en fresh domain q qa HQ HA).
    subst q. apply context_support_member. apply (proj2 (context_member_cons M tb tc tn qa td te tm qa HTarget)).
    now left.
  - apply (context_support_cons M tb tc tn qa td te tm q HTarget). exact (HC f q HF HQ).
Qed.
Lemma quotation_support_context_extend M sb sc sn a su sv sl eb ec en fresh domain tb tc tn qa :
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
  numerical_quotation M a eb ec en fresh domain qa -> environment_cons M sb sc sn a su sv sl ->
  exists td te tm,environment_cons M tb tc tn qa td te tm /\
    quotation_assumptions_supported M su sv sl eb ec en fresh domain td te tm.
Proof.
  intros HC HA HS. destruct (environment_cons_total M tb tc tn qa) as [td [te [tm HT]]].
  exists td,te,tm. split;[exact HT|].
  exact (quotation_assumptions_supported_cons M sb sc sn a su sv sl
    eb ec en fresh domain tb tc tn qa td te tm HC HA HS HT).
Qed.
Lemma quotation_assumptions_supported_rebase M sb sc sn eb ec en k l domain tb tc tn :
  quotation_safe M eb ec en k domain -> quotation_safe M eb ec en l domain ->
  quotation_assumptions_supported M sb sc sn eb ec en k domain tb tc tn ->
  quotation_assumptions_supported M sb sc sn eb ec en l domain tb tc tn.
Proof.
  intros HK HL HC f q HF HQ.
  destruct (numerical_quotation_total M f eb ec en k domain) as [p HP].
  apply (context_support_equivalent M tb tc tn p q (HC f p HF HP)).
  exact (numerical_quotation_rebase_safe M f eb ec en k l domain p q HK HL HP HQ).
Qed.

Print Assumptions source_row_bound_sequent.
Print Assumptions quotation_assumptions_supported_cons.
Print Assumptions quotation_assumptions_supported_rebase.
