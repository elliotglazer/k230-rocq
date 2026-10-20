(** Two-premise FullND rules under the internal relativization invariant. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs
  NumericalContexts NumericalEnvironments NumericalSourceFull SourceSequents
  SourceTraceBounds SourcePropositionalRules SetFormulaCodes SetCodeDescent
  SourceBounded SourceRelativization SourceRelativizationFunctionality
  SourceRelativizedBinaryRules SourceRelativeContexts SourceRelativeContextFacts
  SourceRelativeInvariant SourceRelativeRowBounds.
Unset Implicit Arguments.

Section Rules.
Variable M : Model.
Variables domain bound : carrier M.
Hypothesis HD : source_bounded M domain (succM M (zeroM M)).

Lemma source_relative_IE_row r p q :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_relative_good M domain bound q -> source_case_IE M r p q ->
  source_relative_good M domain bound r.
Proof.
  intros HB [_ [IHP _]] [_ [IHQ _]] [b [c [n [a [d [f [HR [HP [HQ HF]]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n d HB HR).
  intros k u v l rd HK HC HDr.
  destruct (source_relativization_total M domain a) as [ra HA].
  destruct (source_relativization_total M domain f) as [rf HFr].
  apply (full_source_IE M u v l ra rd rf).
  - exact (source_relative_row_sequent_wf M domain bound r b c n d k u v l rd HD HB HR HK HC HDr).
  - exact (IHP b c n f HP k u v l rf HK HC HFr).
  - exact (IHQ b c n a HQ k u v l ra HK HC HA).
  - exact (source_relativized_binary_graph M domain SFImpl a d f ra rd rf
      (or_intror (or_intror eq_refl)) HF HA HDr HFr).
Qed.

Lemma source_relative_CI_row r p q :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_relative_good M domain bound q -> source_case_CI M r p q ->
  source_relative_good M domain bound r.
Proof.
  intros HB [_ [IHP _]] [_ [IHQ _]] [b [c [n [a [d [f [HR [HP [HQ HF]]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG.
  destruct (source_relativization_binary_inv M domain SFAnd a d f g
    (or_introl eq_refl) HF HG) as [ra [rd [HA [HDr HGr]]]].
  apply (full_source_CI M u v l ra rd g).
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - exact (IHP b c n a HP k u v l ra HK HC HA).
  - exact (IHQ b c n d HQ k u v l rd HK HC HDr).
  - exact HGr.
Qed.

Lemma source_relative_BranchPair_row r p q :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_relative_good M domain bound q -> source_case_BranchPair M r p q ->
  source_relative_good M domain bound r.
Proof.
  intros HB [_ [IHP _]] [_ [IHQ _]]
    [b [c [n [a [d [f [x [y [z [s [t [w [HR [HP [HQ [HS HT]]]]]]]]]]]]]]]].
  apply (source_relative_branches_intro M domain bound r b c n a d f HB HR).
  intros k u v l ra rd rf HK HC HA HDr HFr.
  destruct (environment_cons_total M u v l ra) as [u' [v' [l' HCA]]].
  destruct (environment_cons_total M u v l rd) as [u'' [v'' [l'' HCD]]].
  apply (full_source_BranchPair M u v l ra rd rf u' v' l' u'' v'' l'').
  - exact (source_relative_row_branches_wf M domain bound r b c n a d f k u v l ra rd rf
      HD HB HR HK HC HA HDr HFr).
  - apply (IHP x y z f HP k u' v' l' rf HK).
    + exact (source_relative_context_cons M domain b c n k u v l a ra x y z u' v' l' HC HA HS HCA).
    + exact HFr.
  - apply (IHQ s t w f HQ k u'' v'' l'' rf HK).
    + exact (source_relative_context_cons M domain b c n k u v l d rd s t w u'' v'' l'' HC HDr HT HCD).
    + exact HFr.
  - exact HCA.
  - exact HCD.
Qed.

Lemma source_relative_DE_row r p q :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_relative_good M domain bound q -> source_case_DE M r p q ->
  source_relative_good M domain bound r.
Proof.
  intros HB [_ [IHP _]] [_ [_ IHQ]] [b [c [n [a [d [f [disj [HR [HP [HQ HF]]]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l rf HK HC HFr.
  destruct (source_relativization_total M domain a) as [ra HA].
  destruct (source_relativization_total M domain d) as [rd HDr].
  destruct (source_relativization_total M domain disj) as [rdisj HDisj].
  apply (full_source_DE M u v l ra rd rf rdisj).
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l rf HD HB HR HK HC HFr).
  - exact (IHP b c n disj HP k u v l rdisj HK HC HDisj).
  - exact (IHQ b c n a d f HQ k u v l ra rd rf HK HC HA HDr HFr).
  - exact (source_relativized_binary_graph M domain SFOr a d disj ra rd rdisj
      (or_intror (or_introl eq_refl)) HF HA HDr HDisj).
Qed.

Theorem source_relative_prop_binary_row r p q :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_relative_good M domain bound q -> source_prop_binary M r p q ->
  source_relative_good M domain bound r.
Proof.
  intros HB HP HQ [_ [H|[H|[H|H]]]].
  - exact (source_relative_IE_row r p q HB HP HQ H).
  - exact (source_relative_CI_row r p q HB HP HQ H).
  - exact (source_relative_BranchPair_row r p q HB HP HQ H).
  - exact (source_relative_DE_row r p q HB HP HQ H).
Qed.
End Rules.

Print Assumptions source_relative_IE_row.
Print Assumptions source_relative_CI_row.
Print Assumptions source_relative_BranchPair_row.
Print Assumptions source_relative_DE_row.
Print Assumptions source_relative_prop_binary_row.
