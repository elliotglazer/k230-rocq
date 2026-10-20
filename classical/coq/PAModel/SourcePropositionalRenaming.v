(** Finite propositional skeletons commute with actual source renaming;
    their holes are arbitrary internal formulas. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalRenaming
  NumericalSubstitution RenamingSubstitution SourcePropositionalTemplates
  SourcePropositionalSubstitution.
Unset Implicit Arguments.

Theorem source_prop_expression_renaming M rho other b c n delta p f g :
  (forall i,numerical_renaming M (rho i) b c n delta (other i)) ->
  code_relation M rho (source_prop_expression p) f ->
  code_relation M other (source_prop_expression p) g ->
  numerical_renaming M f b c n delta g.
Proof.
  intros HH HF HG.
  apply (proj2 (numerical_renaming_substitution_uniform M f b c n delta g)).
  apply (source_prop_expression_substitution M rho other b c n (addM M n delta) p).
  - intro i. exact (proj1 (numerical_renaming_substitution_uniform M (rho i)
      b c n delta (other i)) (HH i)).
  - exact HF.
  - exact HG.
Qed.

Print Assumptions source_prop_expression_renaming.
