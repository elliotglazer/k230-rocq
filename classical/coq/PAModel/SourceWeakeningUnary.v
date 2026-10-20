From PAModel Require Import Model CodeExpressions NumericalContexts NumericalEnvironments
  NumericalTraces SourceBounded SourcePropositionalRules SourceQuantifierRules SourceSequents
  NumericalSourceFull SourceContextTransport SourceWeakeningInvariant SourceWeakeningRows.
Unset Implicit Arguments.

Theorem source_weakening_base M r : source_prop_base M r -> source_weakening_invariant M r.
Proof.
  intro HRule.
  assert (HO:source_full_row M r).
  { apply trace_derives_base. apply source_full_trace_base. exact HRule. }
  destruct HRule as [_ [H|H]].
  - destruct H as [b [c [n [f [HR HF]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply full_source_Ctx.
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (HI f HF).
  - destruct H as [b [c [n [a [d [x [y [f [HR [HX [HY HF]]]]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_Pc M u v l a d x y f);try assumption.
    exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
Qed.

Theorem source_weakening_prop_unary M r p :
  source_weakening_invariant M p -> source_prop_unary M r p -> source_weakening_invariant M r.
Proof.
  intros HP HRule.
  assert (HO:source_full_row M r).
  { apply (trace_derives_unary M source_full_rules r p (proj1 HP)).
    apply source_full_trace_unary. now left. }
  destruct HRule as [_ [H|[H|[H|[H|[H|H]]]]]].
  - destruct H as [b [c [n [a [d [f [sb [sc [sn [HR [HS [HCons HF]]]]]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC.
    destruct (environment_cons_total M u v l a) as [x [y [z HT]]].
    assert (HA:exists k,source_bounded M a k).
    { apply (source_weakening_assumption_bound M p sb sc sn d a HP HS).
      apply (proj2 (context_member_cons M b c n a sb sc sn a HCons)). now left. }
    apply (full_source_II M u v l a d f x y z).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + apply (proj1 (proj2 HP) sb sc sn d x y z HS).
      * exact (source_context_included_cons M b c n u v l a sb sc sn x y z HI HCons HT).
      * exact (source_context_finite_bound_cons M u v l a x y z HC HA HT).
    + exact HT.
    + exact HF.
  - destruct H as [b [c [n [f [HR HS]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_Exp M u v l f).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n (zeroM M) u v l HS HI HC).
  - destruct H as [b [c [n [a [d [f [HR [HS HF]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n a HO HR).
    intros u v l HI HC. apply (full_source_CE1 M u v l a d f).
    + exact (source_weakening_target_wf M r b c n a u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n f u v l HS HI HC).
    + exact HF.
  - destruct H as [b [c [n [a [d [f [HR [HS HF]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n d HO HR).
    intros u v l HI HC. apply (full_source_CE2 M u v l a d f).
    + exact (source_weakening_target_wf M r b c n d u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n f u v l HS HI HC).
    + exact HF.
  - destruct H as [b [c [n [a [d [f [HR [HS HF]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_DI1 M u v l a d f).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n a u v l HS HI HC).
    + exact HF.
  - destruct H as [b [c [n [a [d [f [HR [HS HF]]]]]]]].
    apply (source_weakening_ordinary_intro M r b c n f HO HR).
    intros u v l HI HC. apply (full_source_DI2 M u v l a d f).
    + exact (source_weakening_target_wf M r b c n f u v l HO HR HC).
    + exact (proj1 (proj2 HP) b c n d u v l HS HI HC).
    + exact HF.
Qed.

Print Assumptions source_weakening_base.
Print Assumptions source_weakening_prop_unary.
