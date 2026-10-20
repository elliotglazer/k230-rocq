(** Move an actual source proof under one fresh existential witness. *)
From PAModel Require Import Model CodeExpressions NumericalContexts NumericalEnvironments
  NumericalRenaming NumericalContextRenaming SourceQuantifierRules NumericalSourceFull
  SourceProofRenaming SourceProofWeakening SourceLeastOrdinalWitness.
Unset Implicit Arguments.

Theorem source_full_prv_shift_cons M b c n sb sc ub uc un body f g k :
  context_shift M b c n sb sc ->environment_cons M sb sc n body ub uc un ->
  context_bounded M ub uc un k ->source_formula_shift M f g ->
  source_full_prv M b c n f ->source_full_prv M ub uc un g.
Proof.
  intros HC HE HB HS HP.
  apply (source_full_prv_weaken_bounded M sb sc n ub uc un g k
    (source_full_prv_renaming M b c n f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 1) sb sc g HP HC HS));[|exact HB].
  exact (source_cons_tail_inclusion M sb sc n body ub uc un HE).
Qed.

Print Assumptions source_full_prv_shift_cons.
