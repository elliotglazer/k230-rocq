(** Actual source proofs moving an internally finite parameter block to a
 larger carrier, and selecting a contiguous subblock. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceMembershipBlocks
 SourceMembershipBlockProofs SourceRawSubset.
Unset Implicit Arguments.
Theorem source_full_membership_block_carrier M start X Y count old new subset b c n k:
 (forall i,coding_lt M i count ->coding_lt M(addM M i start)k)->
 coding_lt M X k->coding_lt M Y k->context_bounded M b c n k->
 source_membership_block M start X count old->source_membership_block M start Y count new->
 source_raw_subset_graph M X Y subset->source_full_prv M b c n old->
 source_full_prv M b c n subset->source_full_prv M b c n new.
Proof.
 intros HNames HX HY HB HOld HNew HSubset POld PSubset.
 apply(source_full_membership_block_intro M start Y count new b c n k HNames HY HNew HB).
 intros i target HI HTarget.
 destruct(sf_relation_total M SFMember(addM M i start)X)as(member&HMember).
 exact(source_full_raw_subset_member M b c n X Y(addM M i start)subset member target
  HSubset HMember HTarget PSubset
  (source_full_membership_block_project M start X count old b c n k i member
   HNames HX HOld HB POld HI HMember)).
Qed.
Theorem source_full_membership_block_slice M start offset carrier total count old new b c n k:
 (forall i,coding_lt M i total ->coding_lt M(addM M i start)k)->
 (forall i,coding_lt M i count ->coding_lt M(addM M i offset)total)->
 coding_lt M carrier k->context_bounded M b c n k->
 source_membership_block M start carrier total old->
 source_membership_block M(addM M offset start)carrier count new->
 source_full_prv M b c n old->source_full_prv M b c n new.
Proof.
 intros HNames HRange HY HB HOld HNew POld.
 assert(HNewNames:forall i,coding_lt M i count ->coding_lt M(addM M i(addM M offset start))k).
 { intros i HI. rewrite (add_assoc M i offset start). exact(HNames _ (HRange i HI)). }
 apply(source_full_membership_block_intro M(addM M offset start)carrier count new b c n k
  HNewNames HY HNew HB).
 intros i target HI HTarget.
 rewrite (add_assoc M i offset start) in HTarget.
 exact(source_full_membership_block_project M start carrier total old b c n k
  (addM M i offset)target HNames HY HOld HB POld(HRange i HI)HTarget).
Qed.
Print Assumptions source_full_membership_block_carrier.
Print Assumptions source_full_membership_block_slice.
