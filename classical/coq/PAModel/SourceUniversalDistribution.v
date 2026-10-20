(** An actual numerical source proof of universal distribution with
    arbitrary internal matrices, not a lift of standard matrix numerals. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone NumericalContexts
  NumericalEnvironments NumericalContextRenaming SourceSequents SourceTraceBounds
  SourceContextTransport NumericalSourceFull SourceShiftSpecialization.
Unset Implicit Arguments.

Lemma source_bounded_universal_from_matrix M a qa k :
  source_bounded M a k -> sf_relation M SFAll a (zeroM M) qa -> source_bounded M qa k.
Proof.
  intros HA HQ. apply (proj2 (source_bounded_accept_unary M SFAll a qa k (or_introl eq_refl) HQ)).
  apply (source_bounded_monotone M a k (succM M k) HA).
  exact (coding_lt_trans M k (succM M k) (succM M (succM M k))
    (coding_lt_succ M k) (coding_lt_succ M (succM M k))).
Qed.

Lemma source_bounded_in_context_wf M b c n f k :
  source_bounded M f k -> source_context_finite_bound M b c n -> source_sequent_wf M b c n f.
Proof.
  intros HF HC. apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) f b c n);
    [|exact HC]. exists k. split;[exact HF|apply context_bounded_empty].
Qed.

Theorem source_full_shifted_universal_hyp M b c n d e a qa k :
  source_context_finite_bound M b c n -> context_shift M b c n d e ->
  context_member M b c n qa -> source_bounded M a k -> sf_relation M SFAll a (zeroM M) qa ->
  source_full_prv M d e n a.
Proof.
  intros HC HS HM HA HQ.
  pose proof (source_context_finite_bound_shift M b c n d e HC HS) as HD.
  destruct (context_renaming_member_forward M b c n (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) d e qa HS HM) as (qs&HQs&HShift).
  destruct (source_shifted_all_specialization M a qa qs k HA HQ HShift) as (ar&HQS&HInst).
  apply (full_source_AllE M d e n ar qs (zeroM M) a).
  - exact (source_bounded_in_context_wf M d e n a k HA HD).
  - apply full_source_Ctx;[|exact HQs].
    destruct HD as [bound HB]. exists bound. split;[exact (HB qs HQs)|exact HB].
  - exact HQS.
  - exact HInst.
Qed.

Theorem source_universal_distribution M a b implication qa qb qimp inside out k :
  source_bounded M a k -> source_bounded M b k ->
  sf_relation M SFImpl a b implication -> sf_relation M SFAll a (zeroM M) qa ->
  sf_relation M SFAll b (zeroM M) qb -> sf_relation M SFAll implication (zeroM M) qimp ->
  sf_relation M SFImpl qa qb inside -> sf_relation M SFImpl qimp inside out ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) out.
Proof.
  intros HA HB HI HQA HQB HQI HIn HOut.
  assert (HImp:source_bounded M implication k).
  { apply (proj2 (source_bounded_accept_binary M SFImpl a b implication k
      ltac:(unfold sf_binary;auto) HI)). auto. }
  pose proof (source_bounded_universal_from_matrix M a qa k HA HQA) as BQA.
  pose proof (source_bounded_universal_from_matrix M b qb k HB HQB) as BQB.
  pose proof (source_bounded_universal_from_matrix M implication qimp k HImp HQI) as BQI.
  assert (BIn:source_bounded M inside k).
  { apply (proj2 (source_bounded_accept_binary M SFImpl qa qb inside k
      ltac:(unfold sf_binary;auto) HIn)). auto. }
  assert (BOut:source_bounded M out k).
  { apply (proj2 (source_bounded_accept_binary M SFImpl qimp inside out k
      ltac:(unfold sf_binary;auto) HOut)). auto. }
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) qimp) as (b1&c1&n1&HC1).
  destruct (environment_cons_total M b1 c1 n1 qa) as (b2&c2&n2&HC2).
  assert (BC1:context_bounded M b1 c1 n1 k).
  { apply (proj2 (context_bounded_cons M _ _ _ qimp b1 c1 n1 k HC1)).
    split;[exact BQI|apply context_bounded_empty]. }
  assert (BC2:context_bounded M b2 c2 n2 k).
  { exact (proj2 (context_bounded_cons M b1 c1 n1 qa b2 c2 n2 k HC2) (conj BQA BC1)). }
  apply (full_source_II M (zeroM M) (zeroM M) (zeroM M) qimp inside out b1 c1 n1).
  - exists k. split;[exact BOut|apply context_bounded_empty].
  - apply (full_source_II M b1 c1 n1 qa qb inside b2 c2 n2).
    + exists k. auto.
    + destruct (context_shift_total M b2 c2 n2) as (d&e&HS).
      apply (full_source_AllI M b2 c2 n2 b qb d e).
      * exists k. auto.
      * pose proof (source_context_finite_bound_shift M b2 c2 n2 d e (ex_intro _ k BC2) HS) as HD.
        apply (full_source_IE M d e n2 a b implication).
        -- exact (source_bounded_in_context_wf M d e n2 b k HB HD).
        -- apply (source_full_shifted_universal_hyp M b2 c2 n2 d e implication qimp k
              (ex_intro _ k BC2) HS);[|exact HImp|exact HQI].
           apply (proj2 (context_member_cons M b1 c1 n1 qa b2 c2 n2 qimp HC2)). right.
           apply (proj2 (context_member_cons M _ _ _ qimp b1 c1 n1 qimp HC1)). now left.
        -- apply (source_full_shifted_universal_hyp M b2 c2 n2 d e a qa k
              (ex_intro _ k BC2) HS);[|exact HA|exact HQA].
           apply (proj2 (context_member_cons M b1 c1 n1 qa b2 c2 n2 qa HC2)). now left.
        -- exact HI.
      * exact HS.
      * exact HQB.
    + exact HC2.
    + exact HIn.
  - exact HC1.
  - exact HOut.
Qed.

Print Assumptions source_full_shifted_universal_hyp.
Print Assumptions source_universal_distribution.
