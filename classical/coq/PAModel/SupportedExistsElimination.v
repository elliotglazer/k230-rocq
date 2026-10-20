(** Existential elimination for arbitrary internally coded source proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent CodeTags
  NumericalProofs NumericalContexts NumericalEnvironments NumericalContextRenaming
  SourceSequents SourceQuantifierRules SourceTraceBounds SourceBounded SetFormulaCodes
  NumericalQuotation QuotationFunctionality QuotationPayloads QuotationHygiene
  QuotationRebase QuotationShift QuotationFormulaFresh QuotedSameBaseRules
  ContextualProofs ContextualDeduction ContextualQuantifiers ContextualGuardedQuantifiers
  SupportedQuotationInvariant SupportedQuotationContext SupportedEigenvariables
  SupportedConjunction ContextSupport.
Unset Implicit Arguments.

Lemma quotation_assumptions_supported_source_cons M sb sc sn a su sv sl
    eb ec en fresh domain tb tc tn qa :
  quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn ->
  numerical_quotation M a eb ec en fresh domain qa -> context_support M tb tc tn qa ->
  environment_cons M sb sc sn a su sv sl ->
  quotation_assumptions_supported M su sv sl eb ec en fresh domain tb tc tn.
Proof.
  intros HS HA HSupport HC f q HF HQ.
  apply (proj1 (context_member_cons M sb sc sn a su sv sl f HC)) in HF.
  destruct HF as [->|HF].
  - assert (q=qa) by exact (numerical_quotation_functional M a eb ec en fresh domain q qa HQ HA).
    now subst q.
  - exact (HS f q HF HQ).
Qed.

Theorem source_supported_exists_elimination M bound r p q :
  source_row_at_bound M r bound -> source_supported_good M bound p ->
  source_supported_good M bound q -> source_case_ExE M r p q ->
  source_supported_good M bound r.
Proof.
  intros HB IHp IHq [b [c [n [a [ex [f [g [u [v [x [y [l
    [Hr [Hp [Hq [HEx [HShift [HSource Hfg]]]]]]]]]]]]]]]]]].
  apply (source_supported_sequent_intro M bound r b c n f HB Hr).
  intros eb ec en fresh domain tb tc tn result HLen HSafe HSupport HDomain HResult.
  destruct (source_row_bound_sequent M r bound b c n f HB Hr) as [HF HContextBound].
  destruct (supported_eigenname_total M eb ec en fresh domain tb tc tn (zeroM M) HSafe)
    as [k [HK [_ [HContext _]]]].
  assert (HKnext : quotation_safe M eb ec en (succM M k) domain)
    by exact (quotation_safe_successor M eb ec en k domain HK).
  destruct (environment_cons_total M eb ec en k) as [fb [fc [fn HEnv]]].
  destruct (numerical_quotation_total M a fb fc fn (succM M k) domain) as [body HBody].
  destruct (quotation_quantifier_total M false k domain body) as [quotedEx HOutput].
  assert (HQuotedEx : numerical_quotation M ex eb ec en k domain quotedEx).
  { exact (numerical_quotation_unary M false a ex eb ec en k domain fb fc fn body quotedEx
      HEx HEnv HBody HOutput). }
  assert (PEx : contextually_provable M tb tc tn quotedEx).
  { exact (proj1 (proj2 IHp) b c n ex Hp eb ec en k domain tb tc tn quotedEx HLen HK
      (quotation_assumptions_supported_rebase M b c n eb ec en fresh k domain tb tc tn
        HSafe HK HSupport) HDomain HQuotedEx). }
  destruct (numerical_quotation_total M f eb ec en (succM M k) domain) as [next HNext].
  assert (HShiftedGoal : numerical_quotation M g fb fc fn (succM M k) domain next).
  { exact (proj1 (quotation_shift_cons_iff M f g bound eb ec en k fb fc fn
      (succM M k) domain next HF Hfg HEnv) HNext). }
  destruct (tagged_pair_total M 1 domain k) as [dom HDom].
  destruct (quotation_binary_total M SFAnd dom body) as [conj HConj].
  destruct (environment_cons_total M tb tc tn conj) as [td [te [tm HTarget]]].
  assert (HConjSupport : context_support M td te tm conj).
  { apply context_support_member. apply (proj2 (context_member_cons M tb tc tn conj td te tm conj HTarget)).
    now left. }
  assert (HDomSupport : context_support M td te tm dom).
  { exact (context_support_conjunction_left M td te tm dom body conj HConj HConjSupport). }
  assert (HBodySupport : context_support M td te tm body).
  { exact (context_support_conjunction_right M td te tm dom body conj HConj HConjSupport). }
  assert (HSRebased : quotation_assumptions_supported M b c n eb ec en (succM M k) domain tb tc tn).
  { exact (quotation_assumptions_supported_rebase M b c n eb ec en fresh (succM M k)
      domain tb tc tn HSafe HKnext HSupport). }
  assert (HSShifted : quotation_assumptions_supported M u v n fb fc fn (succM M k) domain tb tc tn).
  { exact (quotation_assumptions_supported_shift_cons M b c n u v bound eb ec en k
      fb fc fn (succM M k) domain tb tc tn HShift HContextBound HEnv HSRebased). }
  assert (HSFinal : quotation_assumptions_supported M x y l fb fc fn (succM M k) domain td te tm).
  { apply (quotation_assumptions_supported_source_cons M u v n a x y l
      fb fc fn (succM M k) domain td te tm body).
    - exact (quotation_assumptions_supported_target_cons M u v n fb fc fn (succM M k)
        domain tb tc tn conj td te tm HSShifted HTarget).
    - exact HBody.
    - exact HBodySupport.
    - exact HSource. }
  assert (HDFinal : quotation_domains_supported M fb fc fn domain td te tm).
  { exact (quotation_domains_supported_cons M eb ec en k fb fc fn domain td te tm dom
      (quotation_domains_supported_target_cons M eb ec en domain tb tc tn conj td te tm HDomain HTarget)
      HDomSupport HDom HEnv). }
  assert (HNewLen : coding_lt M bound (succM M fn)).
  { rewrite (proj1 HEnv). exact (coding_lt_trans M bound (succM M en)
      (succM M (succM M en)) HLen (coding_lt_succ M (succM M en))). }
  assert (PNext : contextually_provable M td te tm next).
  { exact (proj1 (proj2 IHq) x y l g Hq fb fc fn (succM M k) domain td te tm next
      HNewLen (quotation_safe_cons M eb ec en k domain fb fc fn HK HEnv)
      HSFinal HDFinal HShiftedGoal). }
  destruct (contextual_deduction M tb tc tn conj td te tm next HTarget PNext)
    as [premise [HPremise PPremise]].
  assert (PNextBase : contextually_provable M tb tc tn next).
  { apply (contextual_exists_elimination M tb tc tn k conj next quotedEx premise
      HContext (numerical_quotation_parent_fresh M f eb ec en k domain next HK HNext)).
    - exact (proj1 (quotation_guarded_exists_graph M k domain body dom conj quotedEx
        HDom HConj) HOutput).
    - exact HPremise.
    - exact PEx.
    - exact PPremise. }
  apply (contextual_equivalent_forward M tb tc tn next result
    (numerical_quotation_rebase_safe M f eb ec en (succM M k) fresh domain next result
      HKnext HSafe HNext HResult) PNextBase).
Qed.

Print Assumptions source_supported_exists_elimination.
