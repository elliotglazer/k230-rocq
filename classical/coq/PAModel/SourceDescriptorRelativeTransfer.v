(** Relative refutation transport between unary arithmetic source-axiom
    descriptors. The image family consists of actual internally coded proofs
    in existential closed target axiom contexts; the common context is built
    by PA induction. All derivations use source_full_prv. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalTheories NumericalContexts SourceBounded SetFormulaCodes NumericalSourceFull
  SourceRelativization SourceAxiomContexts SourceContextImages SourceImageContextWitnesses
  SourceDescriptorProvability SourceRelativeTheoryTransfer.
Unset Implicit Arguments.

Definition source_descriptor_relative_axiom_images M S T domain := forall f,
  theory_axiom M S f -> source_bounded M f (zeroM M) -> exists rf,
    source_relativization M domain f rf /\ source_descriptor_provable M T rf.

Theorem source_descriptor_relative_proof_transfer M S T domain ex f rf :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->
  source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M S T domain ->
  source_bounded M rf (zeroM M) -> source_relativization M domain f rf ->
  source_descriptor_provable M S f -> source_descriptor_provable M T rf.
Proof.
  intros HD HEx (eb & ec & en & HE & PEx) HI HRF HRel (b & c & n & HC & HP).
  destruct (source_axiom_image_context_collect_witnesses_with_proof M T domain b c n
    eb ec en ex HE PEx) as (ub & uc & un & HU & PUEx & HImages).
  - intros a HA.
    destruct (HI a (proj2 HC a HA) (proj1 HC a HA)) as (ra & HRA & tb & tc & tn & HT & PT).
    exists ra,tb,tc,tn. auto.
  - exists ub,uc,un. split;[exact HU|].
    exact (source_relative_proof_transfer M domain ex ub uc un b c n f rf
      (proj1 HU) HD HEx PUEx HRF HRel HImages HP).
Qed.

Theorem source_descriptor_relative_refutation_transfer M S T domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->
  source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M S T domain ->
  source_descriptor_provable M S (zeroM M) ->
  source_descriptor_provable M T (zeroM M).
Proof.
  intros HD HE PE HI HP.
  exact (source_descriptor_relative_proof_transfer M S T domain ex (zeroM M) (zeroM M)
    HD HE PE HI (source_bounded_accept_falsity M (zeroM M))
    (source_relativization_falsity M domain) HP).
Qed.

Corollary source_descriptor_relative_consistency_transfer M S T domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->
  source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M S T domain ->
  source_descriptor_consistent M T -> source_descriptor_consistent M S.
Proof.
  intros HD HE PE HI HT HS.
  exact (HT (source_descriptor_relative_refutation_transfer M S T domain ex HD HE PE HI HS)).
Qed.

Print Assumptions source_descriptor_relative_proof_transfer.
Print Assumptions source_descriptor_relative_refutation_transfer.
Print Assumptions source_descriptor_relative_consistency_transfer.
