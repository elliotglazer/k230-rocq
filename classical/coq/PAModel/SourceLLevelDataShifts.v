(** Literal shift transport of chosen common-level data and parameter blocks. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalRenaming NumericalSubstitution RenamingSubstitution
 SourceQuantifierRules NumericalContexts NumericalContextRenaming NumericalSourceFull SourceProofRenaming
 SourceMembershipBlocks SourceMembershipBlockSubstitution SourceCommonLevelPoint SourceCommonLevelWitness
 SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Theorem source_membership_block_shift M start y count old new:
 source_membership_block M start y count old ->source_membership_block M(succM M start)(succM M y)count new ->
 source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 apply(source_membership_block_substitution M start y count old(succM M start)(succM M y)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M y)).
 intros i HI. rewrite source_common_add_successor. exact(source_rec_shift_lookup M(addM M i start)).
Qed.
Theorem source_common_level_point_shift M start count d y old new:
 source_common_level_point M start count d y old ->
 source_common_level_point M(succM M start)count(succM M d)(succM M y)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 apply(source_common_level_point_substitution M start count d y old(succM M start)(succM M d)(succM M y)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M d)(source_rec_shift_lookup M y)).
 intros i HI. rewrite source_common_add_successor. exact(source_rec_shift_lookup M(addM M i start)).
Qed.
Theorem source_full_membership_block_shift M start y count old new b c n u v:
 source_membership_block M start y count old ->source_membership_block M(succM M start)(succM M y)count new ->
 context_shift M b c n u v ->source_full_prv M b c n old ->source_full_prv M u v n new.
Proof.
 intros HO HN HC HP.
 exact(source_full_prv_renaming M b c n old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)u v new HP HC
  (source_membership_block_shift M start y count old new HO HN)).
Qed.
Print Assumptions source_membership_block_shift.
Print Assumptions source_common_level_point_shift.
Print Assumptions source_full_membership_block_shift.
