(** The three unary quantifier cases of the PA-definable source-row
    invariant. The trace's common bound retains instantiation witnesses. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalContexts SourceBounded SourceBoundMonotone SourceSequents SourceTraceBounds
  SourceQuantifierRules SourceRuleBounds SupportedQuotationContext
  SourceRelativization SourceRelativeInvariant SourceRelativeContexts
  SourceRelativeAllI SourceRelativeInstantiation.
Unset Implicit Arguments.

Lemma relative_instantiation_bound M t bound k :
  coding_lt M t bound -> coding_lt M bound (succM M k) -> coding_lt M t k.
Proof.
  intros HT HK. destruct (proj1 (coding_lt_succ_cases M bound k) HK) as [HB|E].
  - exact (coding_lt_trans M t bound k HT HB).
  - now rewrite <- E.
Qed.

Theorem source_relative_AllI_row M domain bound r p :
  source_bounded M domain (code_numeral M 1) ->
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_AllI M r p -> source_relative_good M domain bound r.
Proof.
  intros HD HB [HPB [HPS HPBr]]
    [b [c [n [a [f [bs [cs [HR [HP [HShift HAll]]]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l rf HK HCtx HRF.
  destruct (source_row_bound_sequent M r bound b c n f HB HR) as [HFB HCB].
  destruct (source_relativization_total M domain a) as [ra HRA].
  apply (source_relative_AllI_uniform M domain b c n k a f ra rf u v l bs cs HD
    (source_bounded_monotone M f bound k HFB HK)
    (context_bounded_monotone M b c n bound k HCB HK) HAll HRA HRF HCtx HShift).
  intros tb tc tn HT.
  apply (HPS bs cs n a HP (succM M k) tb tc tn ra).
  - exact (coding_lt_trans M bound (succM M k) (succM M (succM M k))
      HK (coding_lt_succ M (succM M k))).
  - exact HT.
  - exact HRA.
Qed.

Theorem source_relative_AllE_row M domain bound r p :
  source_bounded M domain (code_numeral M 1) ->
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_AllE_at M r p bound -> source_relative_good M domain bound r.
Proof.
  intros HD HB [HPB [HPS HPBr]]
    [b [c [n [a [f [t [g [[HR [HP [HAll HInst]]] HT]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n g HB HR).
  intros k u v l rg HK HCtx HRG.
  destruct (source_row_bound_sequent M r bound b c n g HB HR) as [HGB HCB].
  destruct (source_relativization_total M domain f) as [rf HRF].
  apply (source_relative_AllE M domain b c n k u v l a f t g rf rg HD
    (context_bounded_monotone M b c n bound k HCB HK) HCtx
    (relative_instantiation_bound M t bound k HT HK) HAll HInst HRF HRG).
  exact (HPS b c n f HP k u v l rf HK HCtx HRF).
Qed.

Theorem source_relative_ExI_row M domain bound r p :
  source_bounded M domain (code_numeral M 1) ->
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_ExI_at M r p bound -> source_relative_good M domain bound r.
Proof.
  intros HD HB [HPB [HPS HPBr]]
    [b [c [n [a [f [t [g [[HR [HP [HEx HInst]]] HT]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l rf HK HCtx HRF.
  destruct (source_row_bound_sequent M r bound b c n f HB HR) as [HFB HCB].
  destruct (source_relativization_total M domain g) as [rg HRG].
  apply (source_relative_ExI M domain b c n k u v l a f t g rf rg HD
    (source_bounded_monotone M f bound k HFB HK)
    (context_bounded_monotone M b c n bound k HCB HK) HCtx
    (relative_instantiation_bound M t bound k HT HK) HEx HInst HRF HRG).
  exact (HPS b c n g HP k u v l rg HK HCtx HRG).
Qed.

Theorem source_relative_quantifier_unary M domain bound r p :
  source_bounded M domain (code_numeral M 1) ->
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  (source_case_AllI M r p \/ source_AllE_at M r p bound \/ source_ExI_at M r p bound) ->
  source_relative_good M domain bound r.
Proof.
  intros HD HB HP [HI|[HE|HE]].
  - exact (source_relative_AllI_row M domain bound r p HD HB HP HI).
  - exact (source_relative_AllE_row M domain bound r p HD HB HP HE).
  - exact (source_relative_ExI_row M domain bound r p HD HB HP HE).
Qed.

Print Assumptions source_relative_AllI_row.
Print Assumptions source_relative_AllE_row.
Print Assumptions source_relative_ExI_row.
Print Assumptions source_relative_quantifier_unary.
