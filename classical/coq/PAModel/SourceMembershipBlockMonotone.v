(** The common-level induction's substantive table step: actual raw
    subset transport preserves every internally many parameter members. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourceMembershipBlocks SourceMembershipBlockProofs SourceRawSubset.
Unset Implicit Arguments.

Theorem source_full_membership_block_monotone M start y z n f g subset b c l k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->coding_lt M y k ->coding_lt M z k ->
  source_membership_block M start y n f ->source_membership_block M start z n g ->
  source_raw_subset_graph M y z subset ->context_bounded M b c l k ->
  source_full_prv M b c l f ->source_full_prv M b c l subset ->source_full_prv M b c l g.
Proof.
  intros HNames HY HZ HF HG HSubset HC PF PS.
  apply (source_full_membership_block_intro M start z n g b c l k HNames HZ HG HC).
  intros i right HI HR.
  destruct (sf_relation_total M SFMember (addM M i start) y) as [left HL].
  exact (source_full_raw_subset_member M b c l y z (addM M i start) subset left right
    HSubset HL HR PS (source_full_membership_block_project M start y n f b c l k i left
      HNames HY HF HC PF HI HL)).
Qed.

Print Assumptions source_full_membership_block_monotone.
