From PAModel Require Import Model NumericalContexts NumericalEnvironments NumericalTraces
  SourcePropositionalRules SourceQuantifierRules SourceSequents NumericalSourceFull
  SourceContextTransport SourceWeakeningInvariant SourceWeakeningRows.
Unset Implicit Arguments.

Theorem source_weakening_prop_binary M r p q :
  source_weakening_invariant M p -> source_weakening_invariant M q ->
  source_prop_binary M r p q -> source_weakening_invariant M r.
Proof.
  intros HP HQ HRule.
  assert (HO:source_full_row M r).
  { apply (trace_derives_binary M source_full_rules r p q (proj1 HP) (proj1 HQ)).
    apply source_full_trace_binary. now left. }
  destruct HRule as [_ [H|[H|[H|H]]]].
  - destruct H as [b [c [n [a [d [f [HR [HS [HT HF]]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n d HO HR).
    intros u v l HI HC. apply (full_source_IE M u v l a d f).
    + exact (source_weakening_target_wf M r b c n d u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n f u v l HS HI HC).
    + exact (proj1 (proj2 HQ) b c n a u v l HT HI HC).
    + exact HF.
  - destruct H as [b [c [n [a [d [f [HR [HS [HT HF]]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_CI M u v l a d f).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n a u v l HS HI HC).
    + exact (proj1 (proj2 HQ) b c n d u v l HT HI HC).
    + exact HF.
  - destruct H as (b & c & n & a & d & f & sb & sc & sn & tb & tc & tn & HR & HS & HT & HConsA & HConsD).
    apply (source_weakening_branch_intro M r b c n a d f HO HR).
    intros u v l HI HC.
    destruct (environment_cons_total M u v l a) as [ab [ac [an HA]]].
    destruct (environment_cons_total M u v l d) as [db [dc [dn HD]]].
    pose proof (source_branches_wf_from_row M b c n a d f r HR (source_full_row_wellformed M r HO)) as HW.
    destruct HW as [k [HAB [HDB _]]].
    apply (full_source_BranchPair M u v l a d f ab ac an db dc dn).
    + exact (source_weakening_target_branches_wf M r b c n a d f u v l HO HR HC).
    + apply (proj1 (proj2 HP) sb sc sn f ab ac an HS).
      * exact (source_context_included_cons M b c n u v l a sb sc sn ab ac an HI HConsA HA).
      * apply (source_context_finite_bound_cons M u v l a ab ac an HC);[now exists k|exact HA].
    + apply (proj1 (proj2 HQ) tb tc tn f db dc dn HT).
      * exact (source_context_included_cons M b c n u v l d tb tc tn db dc dn HI HConsD HD).
      * apply (source_context_finite_bound_cons M u v l d db dc dn HC);[now exists k|exact HD].
    + exact HA.
    + exact HD.
  - destruct H as [b [c [n [a [d [f [disj [HR [HS [HT HF]]]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_DE M u v l a d f disj).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n disj u v l HS HI HC).
    + exact (proj2 (proj2 HQ) b c n a d f u v l HT HI HC).
    + exact HF.
Qed.

Print Assumptions source_weakening_prop_binary.
