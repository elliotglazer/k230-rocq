(** Actual source ZFC provability closure under empty-context inclusion
    and modus ponens. Proofs may use different internally finite axiom lists. *)
From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SetCodeDescent
  SourceBounded NumericalContexts ContextCombination SourceSequents SourceTraceBounds
  NumericalSourceFull SourceZFCProvability SourceProofWeakening
  RawSourceImage RawSourceImageInversion RawSourcePropositional RawLogicalRow8.
Unset Implicit Arguments.

Theorem source_zfc_context_union M b c n d e m u v l :
  source_zfc_context M b c n -> source_zfc_context M d e m ->
  context_union M b c n d e m u v l -> source_zfc_context M u v l.
Proof.
  intros HL HR [_ HU] f HF. apply (proj1 (HU f)) in HF.
  destruct HF as [HF|HF];[exact (HL f HF)|exact (HR f HF)].
Qed.

Theorem source_zfc_provable_from_empty M f :
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) f -> source_zfc_provable M f.
Proof.
  intro HP. exists (zeroM M),(zeroM M),(zeroM M). split;[|exact HP].
  intros a HA. exfalso. exact (context_empty M _ _ a HA).
Qed.

Theorem source_zfc_provable_truth M s :
  sf_relation M SFImpl (zeroM M) (zeroM M) s -> source_zfc_provable M s.
Proof.
  intro HS. apply source_zfc_provable_from_empty. apply source_full_truth;[|exact HS].
  exists (zeroM M). split;[|apply context_bounded_empty].
  apply (proj2 (source_bounded_accept_binary M SFImpl (zeroM M) (zeroM M) s
    (zeroM M) ltac:(unfold sf_binary;auto) HS)). split;apply source_bounded_accept_falsity.
Qed.

Theorem source_zfc_provable_mp M a b h :
  source_zfc_provable M a -> source_zfc_provable M h ->
  sf_relation M SFImpl a b h -> source_zfc_provable M b.
Proof.
  intros (ab&ac&an&HAC&HA) (hb&hc&hn&HHC&HH) HImpl.
  destruct (context_union_total M ab ac an hb hc hn) as (ub&uc&un&HU).
  pose proof (source_zfc_context_union M ab ac an hb hc hn ub uc un HAC HHC HU) as HUC.
  pose proof (source_zfc_context_closed M ub uc un HUC) as HUB.
  assert (HA':source_full_prv M ub uc un a).
  { exact (source_full_prv_weaken_bounded M ab ac an ub uc un a (zeroM M) HA
      (context_union_left M ab ac an hb hc hn ub uc un HU) HUB). }
  assert (HH':source_full_prv M ub uc un h).
  { exact (source_full_prv_weaken_bounded M hb hc hn ub uc un h (zeroM M) HH
      (context_union_right M ab ac an hb hc hn ub uc un HU) HUB). }
  destruct (source_full_prv_wellformed M ub uc un h HH') as [k [HB HK]].
  assert (HWB:source_sequent_wf M ub uc un b).
  { exists k. split;[|exact HK].
    exact (proj2 (proj1 (source_bounded_accept_binary M SFImpl a b h k
      ltac:(unfold sf_binary;auto) HImpl) HB)). }
  exists ub,uc,un. split;[exact HUC|].
  exact (full_source_IE M ub uc un a b h HWB HH' HA' HImpl).
Qed.

Theorem source_zfc_raw_row8 M env f sf :
  CodeExpressions.code_relation M env CodeExpressions.code_row8 f ->
  raw_source_image M f sf -> source_zfc_provable M sf.
Proof.
  intros HF HS. apply source_zfc_provable_from_empty.
  exact (raw_row8_source M env f sf HF HS).
Qed.

Print Assumptions source_zfc_provable_truth.
Print Assumptions source_zfc_provable_mp.
Print Assumptions source_zfc_raw_row8.
