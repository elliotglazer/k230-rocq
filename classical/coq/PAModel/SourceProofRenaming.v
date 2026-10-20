(** Full source proof renaming for arbitrary internal proof and map codes.
    The actual numerical renaming/context graphs are the only transform inputs. *)
From PAModel Require Import Model NumericalContextRenaming NumericalRenaming SourceSequents
  NumericalSourceFull SourceProofRenamingInvariant SourceProofRenamingUnary SourceProofRenamingQuantifiers.
Unset Implicit Arguments.

Theorem source_full_row_renaming M r : source_full_row M r -> source_proof_renaming_invariant M r.
Proof.
  apply (source_full_row_induction M (source_proof_renaming_invariant M)).
  - exact (source_proof_renaming_definable M).
  - exact (source_proof_renaming_base M).
  - exact (source_proof_renaming_full_unary M).
  - exact (source_proof_renaming_full_binary M).
Qed.

Theorem source_full_prv_renaming M b c n f rb rc rn delta ub uc g :
  source_full_prv M b c n f -> context_renaming M b c n rb rc rn delta ub uc ->
  numerical_renaming M f rb rc rn delta g -> source_full_prv M ub uc n g.
Proof.
  intros [r [HS HR]] HC HG.
  exact (proj1 (proj2 (source_full_row_renaming M r HR)) b c n f rb rc rn delta ub uc g HS HC HG).
Qed.

Theorem source_full_branches_renaming M b c n a d f rb rc rn delta ub uc ar dr fr :
  source_full_branches M b c n a d f -> context_renaming M b c n rb rc rn delta ub uc ->
  numerical_renaming M a rb rc rn delta ar -> numerical_renaming M d rb rc rn delta dr ->
  numerical_renaming M f rb rc rn delta fr -> source_full_branches M ub uc n ar dr fr.
Proof.
  intros [r [HS HR]] HC HA HD HF.
  exact (proj2 (proj2 (source_full_row_renaming M r HR)) b c n a d f rb rc rn delta ub uc ar dr fr HS HC HA HD HF).
Qed.

Print Assumptions source_full_row_renaming.
Print Assumptions source_full_prv_renaming.
Print Assumptions source_full_branches_renaming.
