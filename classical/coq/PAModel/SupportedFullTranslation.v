(** Full source proofs admit supported quotation in every ordinary PA model.
    One common bound is chosen for the internally finite source trace.
    The induction predicate is the explicit PA formula for supported rows. *)
From PAModel Require Import Model FiniteCoding NumericalTraces NumericalProofs
  NumericalSourceFull SourceSequents SourceQuantifierRules SourceTraceBounds
  SourceRuleBounds SourceBoundedInduction NumericalQuotation QuotationHygiene
  ContextualProofs SupportedQuotationInvariant SupportedPropositional
  SupportedInstantiation SupportedEigenvariables SupportedExistsElimination.
Unset Implicit Arguments.

Lemma source_supported_full_unary M bound r p :
  source_row_at_bound M r bound -> source_supported_good M bound p ->
  source_unary_at M r p bound -> source_supported_good M bound r.
Proof.
  intros HB HP [HProp|[_ [HAll|[HE|HI]]]].
  - exact (source_supported_unary M bound r p HB HP HProp).
  - exact (source_supported_allI M bound r p HB HP HAll).
  - exact (source_supported_all_elimination M bound r p HB HP HE).
  - exact (source_supported_exists_introduction M bound r p HB HP HI).
Qed.

Lemma source_supported_full_binary M bound r p q :
  source_row_at_bound M r bound -> source_supported_good M bound p ->
  source_supported_good M bound q -> source_full_binary M r p q ->
  source_supported_good M bound r.
Proof.
  intros HB HP HQ [HProp|[_ HEx]].
  - exact (source_supported_binary M bound r p q HB HP HQ HProp).
  - exact (source_supported_exists_elimination M bound r p q HB HP HQ HEx).
Qed.

Theorem source_full_supported_trace M b c n :
  trace_sequence M source_full_rules b c (succM M n) ->
  exists bound, forall i r, coding_lt M i (succM M n) -> beta M b c i r ->
    source_supported_good M bound r.
Proof.
  intro HS. destruct (source_trace_uniform_bound M b c (succM M n) HS) as [bound HB].
  exists bound. apply (source_bounded_trace_induction M (source_supported_good M bound)
    b c n bound).
  - exact (source_supported_good_definable M bound).
  - exact (source_supported_base M bound).
  - exact (source_supported_full_unary M bound).
  - exact (source_supported_full_binary M bound).
  - exact HB.
Qed.

Theorem source_full_supported_rows M r :
  source_full_row M r -> exists bound, source_supported_good M bound r.
Proof.
  intros [b [c [n [HS HR]]]].
  destruct (source_full_supported_trace M b c n HS) as [bound HB].
  exists bound. exact (HB n r (coding_lt_succ M n) HR).
Qed.

Theorem source_full_supported_quotation M sb sc sn f :
  source_full_prv M sb sc sn f ->
  exists bound, forall eb ec en fresh domain tb tc tn g,
    coding_lt M bound (succM M en) -> quotation_safe M eb ec en fresh domain ->
    quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
    quotation_domains_supported M eb ec en domain tb tc tn ->
    numerical_quotation M f eb ec en fresh domain g -> contextually_provable M tb tc tn g.
Proof.
  intros [r [HR HP]]. destruct (source_full_supported_rows M r HP) as [bound HB].
  exists bound. exact (proj1 (proj2 HB) sb sc sn f HR).
Qed.

Theorem source_full_supported_branch_quotation M sb sc sn a d f :
  source_full_branches M sb sc sn a d f ->
  exists bound, forall eb ec en fresh domain tb tc tn qa qd qf af df,
    coding_lt M bound (succM M en) -> quotation_safe M eb ec en fresh domain ->
    quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
    quotation_domains_supported M eb ec en domain tb tc tn ->
    numerical_quotation M a eb ec en fresh domain qa ->
    numerical_quotation M d eb ec en fresh domain qd ->
    numerical_quotation M f eb ec en fresh domain qf ->
    implication_graph M qa qf af -> implication_graph M qd qf df ->
    contextually_provable M tb tc tn af /\ contextually_provable M tb tc tn df.
Proof.
  intros [r [HR HP]]. destruct (source_full_supported_rows M r HP) as [bound HB].
  exists bound. exact (proj2 (proj2 HB) sb sc sn a d f HR).
Qed.

Print Assumptions source_full_supported_trace.
Print Assumptions source_full_supported_rows.
Print Assumptions source_full_supported_quotation.
Print Assumptions source_full_supported_branch_quotation.
