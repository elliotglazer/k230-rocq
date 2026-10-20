(** Propositional rule closure for internally coded relativized proofs. *)
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

Lemma source_relative_Ctx_row r :
  source_row_at_bound M r bound -> source_case_Ctx M r ->
  source_relative_good M domain bound r.
Proof.
  intros HB [b [c [n [f [HR HF]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG. apply full_source_Ctx.
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - apply (proj2 (source_relative_context_member_iff M domain b c n k u v l g HC)).
    left. exists f. auto.
Qed.

Lemma source_relative_Pc_row r :
  source_row_at_bound M r bound -> source_case_Pc M r ->
  source_relative_good M domain bound r.
Proof.
  intros HB [b [c [n [a [d [x [y [f [HR [HX [HY HF]]]]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG.
  destruct (source_relativization_total M domain a) as [ra HA].
  destruct (source_relativization_total M domain d) as [rd HDr].
  destruct (source_relativization_total M domain x) as [rx HRX].
  destruct (source_relativization_total M domain y) as [ry HRY].
  apply (full_source_Pc M u v l ra rd rx ry g).
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - exact (source_relativized_binary_graph M domain SFImpl a d x ra rd rx
      (or_intror (or_intror eq_refl)) HX HA HDr HRX).
  - exact (source_relativized_binary_graph M domain SFImpl x a y rx ra ry
      (or_intror (or_intror eq_refl)) HY HRX HA HRY).
  - exact (source_relativized_binary_graph M domain SFImpl y a f ry ra g
      (or_intror (or_intror eq_refl)) HF HRY HA HG).
Qed.

Theorem source_relative_base_row r :
  source_row_at_bound M r bound -> source_prop_base M r ->
  source_relative_good M domain bound r.
Proof.
  intros HB [_ [H|H]].
  - exact (source_relative_Ctx_row r HB H).
  - exact (source_relative_Pc_row r HB H).
Qed.

Lemma source_relative_II_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_II M r p -> source_relative_good M domain bound r.
Proof.
  intros HB [_ [IH _]] [b [c [n [a [d [f [x [y [z [HR [HP [HS HF]]]]]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG.
  destruct (source_relativization_binary_inv M domain SFImpl a d f g
    (or_intror (or_intror eq_refl)) HF HG) as [ra [rd [HA [HDr HGr]]]].
  destruct (environment_cons_total M u v l ra) as [u' [v' [l' HT]]].
  apply (full_source_II M u v l ra rd g u' v' l').
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - apply (IH x y z d HP k u' v' l' rd HK).
    + exact (source_relative_context_cons M domain b c n k u v l a ra x y z u' v' l' HC HA HS HT).
    + exact HDr.
  - exact HT.
  - exact HGr.
Qed.

Lemma source_relative_Exp_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_Exp M r p -> source_relative_good M domain bound r.
Proof.
  intros HB [_ [IH _]] [b [c [n [f [HR HP]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG. apply full_source_Exp.
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - exact (IH b c n (zeroM M) HP k u v l (zeroM M) HK HC
      (source_relativization_falsity M domain)).
Qed.

Lemma source_relative_CE1_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_CE1 M r p -> source_relative_good M domain bound r.
Proof.
  intros HB [_ [IH _]] [b [c [n [a [d [f [HR [HP HF]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n a HB HR).
  intros k u v l ra HK HC HA.
  destruct (source_relativization_total M domain d) as [rd HDr].
  destruct (source_relativization_total M domain f) as [rf HFr].
  apply (full_source_CE1 M u v l ra rd rf).
  - exact (source_relative_row_sequent_wf M domain bound r b c n a k u v l ra HD HB HR HK HC HA).
  - exact (IH b c n f HP k u v l rf HK HC HFr).
  - exact (source_relativized_binary_graph M domain SFAnd a d f ra rd rf
      (or_introl eq_refl) HF HA HDr HFr).
Qed.

Lemma source_relative_CE2_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_CE2 M r p -> source_relative_good M domain bound r.
Proof.
  intros HB [_ [IH _]] [b [c [n [a [d [f [HR [HP HF]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n d HB HR).
  intros k u v l rd HK HC HDr.
  destruct (source_relativization_total M domain a) as [ra HA].
  destruct (source_relativization_total M domain f) as [rf HFr].
  apply (full_source_CE2 M u v l ra rd rf).
  - exact (source_relative_row_sequent_wf M domain bound r b c n d k u v l rd HD HB HR HK HC HDr).
  - exact (IH b c n f HP k u v l rf HK HC HFr).
  - exact (source_relativized_binary_graph M domain SFAnd a d f ra rd rf
      (or_introl eq_refl) HF HA HDr HFr).
Qed.

Lemma source_relative_DI1_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_DI1 M r p -> source_relative_good M domain bound r.
Proof.
  intros HB [_ [IH _]] [b [c [n [a [d [f [HR [HP HF]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG.
  destruct (source_relativization_binary_inv M domain SFOr a d f g
    (or_intror (or_introl eq_refl)) HF HG) as [ra [rd [HA [HDr HGr]]]].
  apply (full_source_DI1 M u v l ra rd g).
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - exact (IH b c n a HP k u v l ra HK HC HA).
  - exact HGr.
Qed.

Lemma source_relative_DI2_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_case_DI2 M r p -> source_relative_good M domain bound r.
Proof.
  intros HB [_ [IH _]] [b [c [n [a [d [f [HR [HP HF]]]]]]]].
  apply (source_relative_sequent_intro M domain bound r b c n f HB HR).
  intros k u v l g HK HC HG.
  destruct (source_relativization_binary_inv M domain SFOr a d f g
    (or_intror (or_introl eq_refl)) HF HG) as [ra [rd [HA [HDr HGr]]]].
  apply (full_source_DI2 M u v l ra rd g).
  - exact (source_relative_row_sequent_wf M domain bound r b c n f k u v l g HD HB HR HK HC HG).
  - exact (IH b c n d HP k u v l rd HK HC HDr).
  - exact HGr.
Qed.

Theorem source_relative_prop_unary_row r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_prop_unary M r p -> source_relative_good M domain bound r.
Proof.
  intros HB HP [_ [H|[H|[H|[H|[H|H]]]]]].
  - exact (source_relative_II_row r p HB HP H).
  - exact (source_relative_Exp_row r p HB HP H).
  - exact (source_relative_CE1_row r p HB HP H).
  - exact (source_relative_CE2_row r p HB HP H).
  - exact (source_relative_DI1_row r p HB HP H).
  - exact (source_relative_DI2_row r p HB HP H).
Qed.
End Rules.

Print Assumptions source_relative_base_row.
Print Assumptions source_relative_prop_unary_row.
