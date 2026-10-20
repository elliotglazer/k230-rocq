(** Support is stable under the context and environment changes needed by
    eigenvariable rules. All indices and fresh names are internal PA values. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions CodeTags CodeDescent NumericalProofs NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalQuotation QuotationHygiene QuotationShift
  SupportedQuotationInvariant SupportedQuotationContext ContextSupport
  SourceBounded ContextualProofs FreshNames SubstitutionEnvironmentTotal
  SourceQuantifierRules SourceSequents SourceTraceBounds QuotationFunctionality
  QuotationRebase QuotedSameBaseRules ContextualGuardedQuantifiers.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma context_above_dividend_fresh M b c n x :
  coding_lt M b x -> context_fresh M b c n x.
Proof.
  intros Hbx f [i [Hi Hf]]. apply formula_above_is_fresh.
  exact (coding_le_lt_trans M f b x
    (remainder_le_dividend M b (beta_modulus M c i) f Hf) Hbx).
Qed.

Lemma quotation_safe_above M b c n k l t :
  quotation_safe M b c n k t -> coding_lt M k l -> quotation_safe M b c n l t.
Proof.
  intros [Ht HE] Hkl. split.
  - exact (coding_lt_trans M t k l Ht Hkl).
  - intros i v HV. exact (coding_lt_trans M v k l (HE i v HV) Hkl).
Qed.

Theorem supported_eigenname_total M eb ec en fresh domain tb tc tn extra :
  quotation_safe M eb ec en fresh domain ->
  exists k, quotation_safe M eb ec en k domain /\ coding_lt M fresh k /\
    context_fresh M tb tc tn k /\ coding_lt M extra k.
Proof.
  intro HS. set (k := succM M (addM M fresh (addM M tb extra))).
  assert (HF : coding_lt M fresh k).
  { unfold k. apply coding_le_add. }
  assert (HT : coding_lt M tb k).
  { unfold k. rewrite (Arithmetic.add_comm M fresh (addM M tb extra)),
      <- (Arithmetic.add_assoc M tb extra fresh). apply coding_le_add. }
  assert (HE : coding_lt M extra k).
  { unfold k. rewrite (Arithmetic.add_comm M tb extra),
      (Arithmetic.add_comm M fresh (addM M extra tb)),
      <- (Arithmetic.add_assoc M extra tb fresh). apply coding_le_add. }
  exists k. split;[exact (quotation_safe_above M eb ec en fresh k domain HS HF)|].
  split;[exact HF|]. split;[exact (context_above_dividend_fresh M tb tc tn k HT)|exact HE].
Qed.

Theorem quotation_assumptions_supported_shift_cons M sb sc sn su sv bound
    eb ec en inserted fb fc fn fresh domain tb tc tn :
  context_shift M sb sc sn su sv -> context_bounded M sb sc sn bound ->
  environment_cons M eb ec en inserted fb fc fn ->
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
  quotation_assumptions_supported M su sv sn fb fc fn fresh domain tb tc tn.
Proof.
  intros HShift HBound HCons HSupport g q HG HQ.
  apply (proj1 (context_renaming_member_iff M sb sc sn (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) su sv g HShift)) in HG.
  destruct HG as [f [HF HFG]].
  apply (HSupport f q HF).
  exact (proj2 (quotation_shift_cons_iff M f g bound eb ec en inserted fb fc fn
    fresh domain q (HBound f HF) HFG HCons) HQ).
Qed.

Theorem quotation_domains_supported_cons M eb ec en inserted fb fc fn domain
    tb tc tn newDom :
  quotation_domains_supported M eb ec en domain tb tc tn ->
  context_support M tb tc tn newDom -> membership_graph M domain inserted newDom ->
  environment_cons M eb ec en inserted fb fc fn ->
  quotation_domains_supported M fb fc fn domain tb tc tn.
Proof.
  intros HD HNew HMember HCons i y d Hi HY HM.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[j E]]; subst i.
  - apply (proj1 (environment_cons_head M eb ec en inserted fb fc fn y HCons)) in HY.
    subst y. assert (d=newDom) by exact (tagged_pair_functional M 1 domain inserted d newDom HM HMember).
    now subst d.
  - apply (proj1 (environment_cons_tail M eb ec en inserted fb fc fn j y HCons)) in HY.
    rewrite (proj1 HCons) in Hi. apply (proj1 (coding_lt_succ_cancel M j en)) in Hi.
    exact (HD j y d Hi HY HM).
Qed.

Corollary quotation_domains_supported_cons_hyp M eb ec en inserted fb fc fn domain
    tb tc tn newDom td te tm :
  quotation_domains_supported M eb ec en domain tb tc tn ->
  membership_graph M domain inserted newDom ->
  environment_cons M eb ec en inserted fb fc fn ->
  environment_cons M tb tc tn newDom td te tm ->
  quotation_domains_supported M fb fc fn domain td te tm.
Proof.
  intros HD HM HE HT. apply (quotation_domains_supported_cons M eb ec en inserted
    fb fc fn domain td te tm newDom).
  - exact (quotation_domains_supported_target_cons M eb ec en domain tb tc tn newDom td te tm HD HT).
  - apply context_support_member. apply (proj2 (context_member_cons M tb tc tn newDom td te tm newDom HT)). now left.
  - exact HM.
  - exact HE.
Qed.

Print Assumptions supported_eigenname_total.
Print Assumptions quotation_assumptions_supported_shift_cons.
Print Assumptions quotation_domains_supported_cons.

Theorem source_supported_allI M bound r p :
  source_row_at_bound M r bound -> source_supported_good M bound p ->
  source_case_AllI M r p -> source_supported_good M bound r.
Proof.
  intros HR HP [b [c [n [a [f [u [v [Hr [Hp [HShift HAll]]]]]]]]]].
  apply (source_supported_sequent_intro M bound r b c n f HR Hr).
  intros eb ec en fresh domain tb tc tn g HLen HSafe HSupport HDomain HQ.
  destruct (source_row_bound_sequent M r bound b c n f HR Hr) as [_ HBound].
  destruct (supported_eigenname_total M eb ec en fresh domain tb tc tn (zeroM M) HSafe)
    as [k [HK [HF [HContext _]]]].
  destruct (numerical_quotation_total M f eb ec en k domain) as [gk HQk].
  apply (contextual_equivalent_forward M tb tc tn gk g
    (numerical_quotation_rebase_safe M f eb ec en k fresh domain gk g HK HSafe HQk HQ)).
  destruct (numerical_quotation_unary_inv M true a f eb ec en k domain gk HAll HQk)
    as [fb [fc [fn [body [HEnv [HBody HOutput]]]]]].
  destruct (tagged_pair_total M 1 domain k) as [dom HDom].
  destruct (environment_cons_total M tb tc tn dom) as [td [te [tm HTarget]]].
  apply (contextual_guarded_all_intro M tb tc tn k domain body dom td te tm gk
    HDom HTarget HContext);[|exact HOutput].
  assert (HKsucc : quotation_safe M eb ec en (succM M k) domain)
    by exact (quotation_safe_successor M eb ec en k domain HK).
  assert (HSrebase : quotation_assumptions_supported M b c n eb ec en
    (succM M k) domain tb tc tn).
  { exact (quotation_assumptions_supported_rebase M b c n eb ec en fresh
      (succM M k) domain tb tc tn HSafe HKsucc HSupport). }
  assert (HSshift : quotation_assumptions_supported M u v n fb fc fn
    (succM M k) domain tb tc tn).
  { exact (quotation_assumptions_supported_shift_cons M b c n u v bound eb ec en
      k fb fc fn (succM M k) domain tb tc tn HShift HBound HEnv HSrebase). }
  assert (HNewLen : coding_lt M bound (succM M fn)).
  { rewrite (proj1 HEnv). exact (coding_lt_trans M bound (succM M en)
      (succM M (succM M en)) HLen (coding_lt_succ M (succM M en))). }
  exact (proj1 (proj2 HP) u v n a Hp fb fc fn (succM M k) domain td te tm body
    HNewLen (quotation_safe_cons M eb ec en k domain fb fc fn HK HEnv)
    (quotation_assumptions_supported_target_cons M u v n fb fc fn (succM M k)
      domain tb tc tn dom td te tm HSshift HTarget)
    (quotation_domains_supported_cons_hyp M eb ec en k fb fc fn domain
      tb tc tn dom td te tm HDomain HDom HEnv HTarget) HBody).
Qed.

Print Assumptions source_supported_allI.
