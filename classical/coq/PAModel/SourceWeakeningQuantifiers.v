From PAModel Require Import Model CodeExpressions NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalTraces SourceBounded SourcePropositionalRules
  SourceQuantifierRules SourceSequents NumericalSourceFull SourceContextTransport
  SourceWeakeningInvariant SourceWeakeningRows SourceWeakeningUnary SourceWeakeningBinary.
Unset Implicit Arguments.

Theorem source_weakening_full_unary M r p :
  source_weakening_invariant M p -> source_full_unary M r p -> source_weakening_invariant M r.
Proof.
  intros HP HRule.
  assert (HO:source_full_row M r).
  { apply (trace_derives_unary M source_full_rules r p (proj1 HP)).
    apply source_full_trace_unary. exact HRule. }
  destruct HRule as [H|[_ [H|[H|H]]]].
  - exact (source_weakening_prop_unary M r p HP H).
  - destruct H as (b & c & n & a & f & sb & sc & HR & HS & HShift & HF).
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC.
    destruct (context_shift_total M u v l) as [ub [uc HT]].
    apply (full_source_AllI M u v l a f ub uc).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + apply (proj1 (proj2 HP) sb sc n a ub uc l HS).
      * exact (source_context_included_shift M b c n u v l sb sc ub uc HI HShift HT).
      * exact (source_context_finite_bound_shift M u v l ub uc HC HT).
    + exact HT.
    + exact HF.
  - destruct H as (b & c & n & a & f & t & g & HR & HS & HF & HG).
    apply (source_weakening_ordinary_intro M r b c n g HO HR).
    intros u v l HI HC. apply (full_source_AllE M u v l a f t g).
    + exact (source_weakening_target_wf M r b c n g u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n f u v l HS HI HC).
    + exact HF.
    + exact HG.
  - destruct H as (b & c & n & a & f & t & g & HR & HS & HF & HG).
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_ExI M u v l a f t g).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n g u v l HS HI HC).
    + exact HF.
    + exact HG.
Qed.

Theorem source_weakening_full_binary M r p q :
  source_weakening_invariant M p -> source_weakening_invariant M q ->
  source_full_binary M r p q -> source_weakening_invariant M r.
Proof.
  intros HP HQ HRule.
  assert (HO:source_full_row M r).
  { apply (trace_derives_binary M source_full_rules r p q (proj1 HP) (proj1 HQ)).
    apply source_full_trace_binary. exact HRule. }
  destruct HRule as [H|[_ H]].
  - exact (source_weakening_prop_binary M r p q HP HQ H).
  - destruct H as (b & c & n & a & ex & f & g & sb & sc & tb & tc & tn & HR & HS & HBranch & HEx & HShift & HCons & HF).
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC.
    destruct (context_shift_total M u v l) as [ub [uc HT]].
    destruct (environment_cons_total M ub uc l a) as [vb [vc [vn HNew]]].
    assert (HA:exists k,source_bounded M a k).
    { apply (source_weakening_assumption_bound M q tb tc tn g a HQ HBranch).
      apply (proj2 (context_member_cons M sb sc n a tb tc tn a HCons)). now left. }
    assert (HB:source_context_finite_bound M ub uc l).
    { exact (source_context_finite_bound_shift M u v l ub uc HC HT). }
    apply (full_source_ExE M u v l a ex f g ub uc vb vc vn).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n ex u v l HS HI HC).
    + apply (proj1 (proj2 HQ) tb tc tn g vb vc vn HBranch).
      * apply (source_context_included_cons M sb sc n ub uc l a tb tc tn vb vc vn);try assumption.
        exact (source_context_included_shift M b c n u v l sb sc ub uc HI HShift HT).
      * exact (source_context_finite_bound_cons M ub uc l a vb vc vn HB HA HNew).
    + exact HEx.
    + exact HT.
    + exact HNew.
    + exact HF.
Qed.

Print Assumptions source_weakening_full_unary.
Print Assumptions source_weakening_full_binary.
