(** Existential elimination preserves the combined-context source-row
    invariant. The branch context has the explicit body and domain heads. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalContexts NumericalEnvironments NumericalContextRenaming
  SourceBounded SourceBoundMonotone SourceSequents SourceTraceBounds
  SourceQuantifierRules SupportedQuotationContext SourceRelativization
  SourceRelativeInvariant SourceRelativeContexts SourceRelativeContextFacts
  SourceRelativizedExistsTwo.
Unset Implicit Arguments.

Theorem source_relative_ExE_row M domain bound r p q :
  source_bounded M domain (code_numeral M 1) ->
  source_row_at_bound M r bound ->
  source_relative_good M domain bound p -> source_relative_good M domain bound q ->
  source_case_ExE M r p q -> source_relative_good M domain bound r.
Proof.
  intros HD HB [HPB [HPS HPBr]] [HQB [HQS HQBr]] HCase.
  destruct HCase as (b & c & n & a & ex & f & g & bs & cs & xb & xc & xn &
    HR & HP & HQ & HEx & HShift & HCons & HConclusion).
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l rf HK HCtx HRF.
  destruct (source_row_bound_sequent M r bound b c n f HB HR) as [HFB HCB].
  destruct (source_relativization_total M domain a) as [ra HRA].
  destruct (source_relativization_total M domain ex) as [rex HREx].
  destruct (source_relativization_total M domain g) as [rg HRG].
  destruct (context_shift_total M u v l) as [su [sv HS]].
  destruct (environment_cons_total M su sv l domain) as [du [dv [dn HDCons]]].
  destruct (environment_cons_total M du dv dn ra) as [au [av [an HBCons]]].
  assert (HShiftCtx:source_relative_context M domain bs cs n (succM M k) du dv dn).
  { exact (source_relative_context_shift_cons M domain b c n k u v l
      bs cs su sv du dv dn HD HCtx HShift HS HDCons). }
  assert (HBranchCtx:source_relative_context M domain xb xc xn (succM M k) au av an).
  { exact (source_relative_context_cons M domain bs cs n (succM M k) du dv dn
      a ra xb xc xn au av an HShiftCtx HRA HCons HBCons). }
  apply (source_relativized_ExE_two M domain a ex f g ra rex rf rg
    u v l su sv du dv dn au av an k HD
    (source_bounded_monotone M f bound k HFB HK)
    (source_relative_context_bounded M domain b c n k u v l HD
      (context_bounded_monotone M b c n bound k HCB HK) HCtx)
    HEx HConclusion HRA HREx HRF HRG HS HDCons HBCons).
  - exact (HPS b c n ex HP k u v l rex HK HCtx HREx).
  - apply (HQS xb xc xn g HQ (succM M k) au av an rg).
    + exact (coding_lt_trans M bound (succM M k) (succM M (succM M k))
        HK (coding_lt_succ M (succM M k))).
    + exact HBranchCtx.
    + exact HRG.
Qed.

Print Assumptions source_relative_ExE_row.
