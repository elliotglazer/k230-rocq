(** Every genuine unary source instance commutes with an arbitrary numerical renaming. *)
From PAModel Require Import Model CodeExpressions SourceBounded NumericalRenamingMaps NumericalRenaming
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution SourceUnarySubstitution.
Unset Implicit Arguments.
Theorem source_unary_instance_renaming_graph M p x px rb rc rn delta y py :
 source_bounded M p(code_numeral M 1) ->numerical_instantiation M p x px ->
 renaming_lookup M rb rc rn delta x y ->numerical_instantiation M p y py ->numerical_renaming M px rb rc rn delta py.
Proof.
 intros BP HP HX HY. apply(proj2(numerical_renaming_substitution_uniform M px rb rc rn delta py)).
 apply(source_domain_instance_substitution_graph M p x px rb rc rn(addM M rn delta)y py BP HP).
 - exact(proj1(renaming_substitution_lookup M rb rc rn delta x y)HX).
 - exact HY.
Qed.
Print Assumptions source_unary_instance_renaming_graph.
