(** Actual ZFC source proof renaming and canonical named generalization.
    Closed axiom contexts keep exactly the same source axiom members. *)
From PAModel Require Import Model NumericalRenaming NumericalContextRenaming
  SourceProofRenaming SourceZFCProvability SourceZFCGeneralization
  RawSourceProofTransfer.
Unset Implicit Arguments.

Theorem source_zfc_provable_renaming M f rb rc rn delta g :
  source_zfc_provable M f -> numerical_renaming M f rb rc rn delta g ->
  source_zfc_provable M g.
Proof.
  intros (b&c&n&HC&HP) HR.
  destruct (context_renaming_total M b c n rb rc rn delta) as (ub&uc&HCR).
  exists ub,uc,n. split.
  - exact (source_zfc_context_renaming M b c n rb rc rn delta ub uc HC HCR).
  - exact (source_full_prv_renaming M b c n f rb rc rn delta ub uc g HP HCR HR).
Qed.

Theorem source_zfc_raw_named_generalization M :
  raw_named_generalization_closure M (source_zfc_provable M).
Proof.
  intros s x b c v out HP HB HR HA.
  exact (source_zfc_provable_all M v out
    (source_zfc_provable_renaming M s b c _ _ v HP HR) HA).
Qed.

Print Assumptions source_zfc_provable_renaming.
Print Assumptions source_zfc_raw_named_generalization.
