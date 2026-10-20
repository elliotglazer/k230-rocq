(** Exact shift graphs for the fixed hierarchy predicates in reflection. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalInstantiation
  NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceFiniteCutoffShift
  SourceHierarchySyntax SourceRawSubset SourceSubsetSubstitution SourceUnarySubstitution.
Unset Implicit Arguments.

Theorem source_LL_shift_to M d z f g :source_LL_instance M d z f ->
  source_LL_instance M (succM M d) (succM M z) g ->source_formula_shift M f g.
Proof.
  intros HF HG. apply (proj2 (numerical_renaming_empty_substitution M f (zeroM M) (zeroM M)
    (code_numeral M 1) g)).
  exact (source_LL_instance_substitution M d z f (succM M d) (succM M z) g
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) HF HG
    (source_cutoff_shift_base_lookup M d) (source_cutoff_shift_base_lookup M z)).
Qed.

Theorem source_raw_subset_shift_to M d e f g :source_raw_subset_graph M d e f ->
  source_raw_subset_graph M (succM M d) (succM M e) g ->source_formula_shift M f g.
Proof.
  intros HF HG. apply (proj2 (numerical_renaming_empty_substitution M f (zeroM M) (zeroM M)
    (code_numeral M 1) g)).
  exact (source_oc_subset_substitution M d e f (succM M d) (succM M e) g
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) HF
    (source_cutoff_shift_base_lookup M d) (source_cutoff_shift_base_lookup M e) HG).
Qed.

Theorem source_domain_shift_to M domain x f g :source_bounded M domain (code_numeral M 1) ->
  numerical_instantiation M domain x f ->numerical_instantiation M domain (succM M x) g ->
  source_formula_shift M f g.
Proof.
  intros HD HF HG. apply (proj2 (numerical_renaming_empty_substitution M f (zeroM M) (zeroM M)
    (code_numeral M 1) g)).
  exact (source_domain_instance_substitution_graph M domain x f
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) (succM M x) g HD HF
    (source_cutoff_shift_base_lookup M x) HG).
Qed.

Print Assumptions source_LL_shift_to.
Print Assumptions source_raw_subset_shift_to.
Print Assumptions source_domain_shift_to.
