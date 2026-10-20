(** Closed axiom contexts are unchanged by every source variable renaming.
    Ordinary universal introduction is therefore an actual ZFC proof rule. *)
From PAModel Require Import Model FiniteCoding FiniteCRT NumericalContexts
  NumericalRenaming NumericalContextRenaming SourceRenamingIdentity SourceBoundMonotone
  SourceBounded SetFormulaCodes SourceSequents SourceQuantifierRules NumericalSourceFull
  SourceZFCProvability SourceProofWeakening.
Unset Implicit Arguments.

Theorem numerical_renaming_closed_identity M f p q m delta g :
  source_bounded M f (zeroM M) -> numerical_renaming M f p q m delta g -> g=f.
Proof.
  intros HF HR. apply (numerical_renaming_functional M f p q m delta g f HR).
  apply (numerical_renaming_identity_on_bound M f p q m delta (zeroM M) HF).
  intros i Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Theorem context_renaming_closed_members M b c n p q m delta d e :
  context_bounded M b c n (zeroM M) ->
  context_renaming M b c n p q m delta d e ->
  forall f,context_member M d e n f <-> context_member M b c n f.
Proof.
  intros HB HR f. rewrite (context_renaming_member_iff M b c n p q m delta d e f HR).
  split.
  - intros (g&HG&HGF). rewrite (numerical_renaming_closed_identity M g p q m delta f (HB g HG) HGF).
    exact HG.
  - intro HF. exists f. split;[exact HF|].
    apply (numerical_renaming_identity_on_bound M f p q m delta (zeroM M) (HB f HF)).
    intros i Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Theorem source_zfc_context_renaming M b c n p q m delta d e :
  source_zfc_context M b c n -> context_renaming M b c n p q m delta d e ->
  source_zfc_context M d e n.
Proof.
  intros HC HR f HF. apply HC.
  exact (proj1 (context_renaming_closed_members M b c n p q m delta d e
    (source_zfc_context_closed M b c n HC) HR f) HF).
Qed.

Theorem source_zfc_provable_all M a f :
  source_zfc_provable M a -> sf_relation M SFAll a (zeroM M) f ->
  source_zfc_provable M f.
Proof.
  intros (b&c&n&HC&HP) HF.
  destruct (context_shift_total M b c n) as (d&e&HS).
  pose proof (source_zfc_context_closed M b c n HC) as HB.
  pose proof (source_zfc_context_renaming M b c n _ _ _ _ d e HC HS) as HD.
  assert (HI:context_included M b c n d e n).
  { intros g HG. exact (proj2 (context_renaming_closed_members M b c n _ _ _ _ d e HB HS g) HG). }
  pose proof (source_full_prv_weaken_bounded M b c n d e n a (zeroM M) HP HI
    (source_zfc_context_closed M d e n HD)) as HP'.
  destruct (source_full_prv_wellformed M b c n a HP) as (k&HAB&HCB).
  assert (HWF:source_sequent_wf M b c n f).
  { exists k. split;[|exact HCB].
    apply (proj2 (source_bounded_accept_unary M SFAll a f k (or_introl eq_refl) HF)).
    apply (source_bounded_monotone M a k (succM M k) HAB).
    exact (coding_lt_trans M k (succM M k) (succM M (succM M k))
      (coding_lt_succ M k) (coding_lt_succ M (succM M k))). }
  exists b,c,n. split;[exact HC|]. exact (full_source_AllI M b c n a f d e HWF HP' HS HF).
Qed.

Print Assumptions numerical_renaming_closed_identity.
Print Assumptions context_renaming_closed_members.
Print Assumptions source_zfc_provable_all.
