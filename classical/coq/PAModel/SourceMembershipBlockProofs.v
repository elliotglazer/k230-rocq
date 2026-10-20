(** Actual source proof operations for the internally finite table of
    parameter-membership assertions used by L_common. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded SourceQuantifierRules NumericalContexts NumericalSourceFull SetFormulaCodes
  NumericalRenaming NumericalRenamingMaps NumericalContextRenaming
  SourceContextConjunction SourceContextConjunctionProofs SourceContextConjunctionRenaming
  SourceMembershipBlocks.
Unset Implicit Arguments.

Lemma source_membership_context_bound M start y n b c k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->coding_lt M y k ->
  source_membership_context M start y n b c ->context_bounded M b c n k.
Proof.
  intros HNames HY HCtx f [i [HI HF]].
  exact (proj2 (source_bounded_accept_atom M SFMember (addM M i start) y f k
    (or_introl eq_refl)(HCtx i f HI HF)) (conj (HNames i HI) HY)).
Qed.
Theorem source_membership_block_bound M start y n result k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->coding_lt M y k ->
  source_membership_block M start y n result ->source_bounded M result k.
Proof.
  intros HNames HY [b [c [HC HF]]].
  exact (source_context_conjunction_bound M b c n result k HF
    (source_membership_context_bound M start y n b c k HNames HY HC)).
Qed.
Theorem source_full_membership_block_intro M start y n result b c l k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->coding_lt M y k ->
  source_membership_block M start y n result ->context_bounded M b c l k ->
  (forall i f,coding_lt M i n ->sf_relation M SFMember (addM M i start) y f ->source_full_prv M b c l f) ->
  source_full_prv M b c l result.
Proof.
  intros HNames HY [sb [sc [HSC HF]]] HC HH.
  assert (PH:forall h,context_member M sb sc n h ->source_full_prv M b c l h).
  { intros h [i [HI HHCode]]. exact (HH i h HI (HSC i h HI HHCode)). }
  exact (proj2 (source_context_conjunction_intro M n sb sc result b c l k HF
    (source_membership_context_bound M start y n sb sc k HNames HY HSC) HC PH)).
Qed.
Theorem source_full_membership_block_project M start y n result b c l k i f :
  (forall j,coding_lt M j n ->coding_lt M (addM M j start) k) ->coding_lt M y k ->
  source_membership_block M start y n result ->context_bounded M b c l k ->
  source_full_prv M b c l result ->coding_lt M i n ->sf_relation M SFMember (addM M i start) y f ->
  source_full_prv M b c l f.
Proof.
  intros HNames HY [sb [sc [HSC HF]]] HC PP HI HAtom.
  destruct (beta_total M sb sc i) as [g HG].
  pose proof (sf_relation_functional M SFMember (addM M i start) y f g HAtom (HSC i g HI HG)) as E. subst g.
  exact (source_context_conjunction_project M n sb sc result b c l k HF
    (source_membership_context_bound M start y n sb sc k HNames HY HSC) HC PP f (ex_intro _ i (conj HI HG))).
Qed.

Theorem source_membership_block_renaming M start y n f start' y' g rb rc rn delta :
  source_membership_block M start y n f ->source_membership_block M start' y' n g ->
  renaming_lookup M rb rc rn delta y y' ->
  (forall i,coding_lt M i n ->renaming_lookup M rb rc rn delta (addM M i start)(addM M i start')) ->
  numerical_renaming M f rb rc rn delta g.
Proof.
  intros [sb [sc [HS HF]]] [tb [tc [HT HG]]] HY HNames.
  apply (source_context_conjunction_renaming M sb sc tb tc rb rc rn delta n f g HF HG).
  intros i a b HI HA HB.
  apply (proj2 (numerical_renaming_member M (addM M i start) y a rb rc rn delta b (HS i a HI HA))).
  exists (addM M i start'),y'. split;[exact (HNames i HI)|]. split;[exact HY|exact (HT i b HI HB)].
Qed.
Theorem source_membership_block_shift M start y n f g :
  source_membership_block M start y n f ->source_membership_block M (succM M start)(succM M y) n g ->
  source_formula_shift M f g.
Proof.
  intros HF HG. apply (source_membership_block_renaming M start y n f (succM M start)(succM M y) g
    (zeroM M)(zeroM M)(zeroM M)(succM M (zeroM M)) HF HG).
  - apply context_shift_lookup. reflexivity.
  - intros i HI. apply context_shift_lookup. rewrite (Arithmetic.add_comm M i (succM M start)),
      Arithmetic.add_succ,(Arithmetic.add_comm M start i). reflexivity.
Qed.

Print Assumptions source_membership_block_bound.
Print Assumptions source_full_membership_block_intro.
Print Assumptions source_full_membership_block_project.
Print Assumptions source_membership_block_renaming.
Print Assumptions source_membership_block_shift.
