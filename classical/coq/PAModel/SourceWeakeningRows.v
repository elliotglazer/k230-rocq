From PAModel Require Import Model NumericalContexts SourceBounded SourceSequents NumericalSourceFull
  SourceContextTransport SourceWeakeningInvariant.
Unset Implicit Arguments.

Lemma source_weakening_ordinary_intro M r b c n f :
  source_full_row M r -> source_sequent M b c n f r ->
  (forall u v l,context_included M b c n u v l -> source_context_finite_bound M u v l ->
    source_full_prv M u v l f) -> source_weakening_invariant M r.
Proof.
  intros HR HS HP. split;[exact HR|]. split.
  - intros b' c' n' f' u v l HS' HI HC.
    destruct (source_sequent_injective M b c n f b' c' n' f' r HS HS') as [E1 [E2 [E3 E4]]].
    subst b' c' n' f'. exact (HP u v l HI HC).
  - intros b' c' n' a d g u v l HB _ _. exfalso.
    exact (source_row_kinds_disjoint M b c n f b' c' n' a d g r HS HB).
Qed.

Lemma source_weakening_branch_intro M r b c n a d f :
  source_full_row M r -> source_branches M b c n a d f r ->
  (forall u v l,context_included M b c n u v l -> source_context_finite_bound M u v l ->
    source_full_branches M u v l a d f) -> source_weakening_invariant M r.
Proof.
  intros HR HS HP. split;[exact HR|]. split.
  - intros b' c' n' g u v l HG _ _. exfalso.
    exact (source_row_kinds_disjoint M b' c' n' g b c n a d f r HG HS).
  - intros b' c' n' a' d' f' u v l HS' HI HC.
    destruct (source_branches_injective M b c n a d f b' c' n' a' d' f' r HS HS')
      as [E1 [E2 [E3 [E4 [E5 E6]]]]].
    subst b' c' n' a' d' f'. exact (HP u v l HI HC).
Qed.

Lemma source_weakening_target_wf M r b c n f u v l :
  source_full_row M r -> source_sequent M b c n f r -> source_context_finite_bound M u v l ->
  source_sequent_wf M u v l f.
Proof.
  intros HR HS HC. apply (source_wf_transport_context M b c n f u v l);[|exact HC].
  exact (source_sequent_wf_from_row M b c n f r HS (source_full_row_wellformed M r HR)).
Qed.

Lemma source_weakening_target_branches_wf M r b c n a d f u v l :
  source_full_row M r -> source_branches M b c n a d f r -> source_context_finite_bound M u v l ->
  source_branches_wf M u v l a d f.
Proof.
  intros HR HS HC. apply (source_branches_wf_transport_context M b c n a d f u v l);[|exact HC].
  exact (source_branches_wf_from_row M b c n a d f r HS (source_full_row_wellformed M r HR)).
Qed.

Lemma source_weakening_assumption_bound M p b c n f a :
  source_weakening_invariant M p -> source_sequent M b c n f p -> context_member M b c n a ->
  exists k,source_bounded M a k.
Proof.
  intros HP HS HA.
  destruct (source_full_prv_wellformed M b c n f (source_weakening_original_sequent M p b c n f HP HS))
    as [k [_ HC]]. exists k. exact (HC a HA).
Qed.

Print Assumptions source_weakening_ordinary_intro.
Print Assumptions source_weakening_branch_intro.
Print Assumptions source_weakening_target_wf.
