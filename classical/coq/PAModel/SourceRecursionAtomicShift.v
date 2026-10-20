(** Ordinary shift graphs for the recursion's atomic guards. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
 NumericalRenaming NumericalRenamingMaps NumericalContextRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Theorem source_rec_member_shift M x y old new:
 sf_relation M SFMember x y old ->sf_relation M SFMember(succM M x)(succM M y)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_member M x y old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new HO)).
 exists(succM M x),(succM M y). repeat split;try assumption;apply context_shift_lookup;reflexivity.
Qed.
Theorem source_rec_successor_shift M x y old new:
 source_rec_successor M x y old ->source_rec_successor M(succM M x)(succM M y)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_successor_substitution M x y old(succM M x)(succM M y)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M x)(source_rec_shift_lookup M y)).
Qed.
Print Assumptions source_rec_member_shift.
Print Assumptions source_rec_successor_shift.
