(** The internal transposition is genuinely involutive on valid source
    formulas and finite contexts, so proofs can be pulled back from final roles. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  SourceZeroTransposition SourceCarrierRenaming SourceRenamingDiamond SourceRenamingIdentity
  SourceShiftSpecialization NumericalRenamingMaps NumericalRenaming NumericalContexts
  NumericalContextRenaming NumericalSourceFull SourceProofRenaming.
Unset Implicit Arguments.

Theorem source_zero_transposition_formula_reverse M fresh b c f g k :
  source_zero_transposition M fresh b c ->source_bounded M f k ->
  numerical_renaming M f b c (succM M fresh)(zeroM M) g ->
  numerical_renaming M g b c (succM M fresh)(zeroM M) f.
Proof.
  intros HM HF HR.
  pose proof (source_valid_identity M f k HF) as HI.
  apply (numerical_source_renaming_diamond M f k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) b c (succM M fresh)(zeroM M)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) b c (succM M fresh)(zeroM M) f g f HF HI HR HI).
  intros i j l m _ HJ HJM HL.
  pose proof (renaming_lookup_functional M _ _ _ _ _ j i HJ (source_empty_renaming_lookup M i)) as E. subst j.
  pose proof (renaming_lookup_functional M _ _ _ _ _ m i HJM (source_empty_renaming_lookup M i)) as E. subst m.
  apply HM. apply source_zero_transposition_index_symmetric. exact (proj1 (HM i l) HL).
Qed.

Theorem source_zero_transposition_context_reverse M fresh b c cb cc cn db dc k :
  source_zero_transposition M fresh b c ->context_bounded M cb cc cn k ->
  context_renaming M cb cc cn b c (succM M fresh)(zeroM M) db dc ->
  context_renaming M db dc cn b c (succM M fresh)(zeroM M) cb cc.
Proof.
  intros HM HB HC i f g HI HF HG.
  exact (source_zero_transposition_formula_reverse M fresh b c g f k HM
    (HB g ltac:(exists i;auto)) (HC i g f HI HG HF)).
Qed.

Theorem source_zero_transposition_proof_pullback M fresh b c cb cc cn db dc f g k :
  source_zero_transposition M fresh b c ->source_bounded M f k ->
  numerical_renaming M f b c (succM M fresh)(zeroM M) g ->
  context_renaming M cb cc cn b c (succM M fresh)(zeroM M) db dc ->
  source_full_prv M cb cc cn g ->source_full_prv M db dc cn f.
Proof.
  intros HM HF HR HC PG.
  exact (source_full_prv_renaming M cb cc cn g b c (succM M fresh)(zeroM M) db dc f PG HC
    (source_zero_transposition_formula_reverse M fresh b c f g k HM HF HR)).
Qed.

Print Assumptions source_zero_transposition_formula_reverse.
Print Assumptions source_zero_transposition_context_reverse.
Print Assumptions source_zero_transposition_proof_pullback.
