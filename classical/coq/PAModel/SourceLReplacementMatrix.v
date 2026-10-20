(** The actual psiR matrix at the Separation image is exactly the
    Replacement witness predicate, including every nonstandard parameter. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceLMatrixRecipes SourceRelativization SourceFiniteCutoffShift SourceQfFunctionality
 SourceLReplacementPsiR SourceReplacementCutoff SchemaRenamingDescriptors NumericalRenaming SetSchemaConstructors.
Unset Implicit Arguments.
Theorem source_L_psiR_Replacement_matrix M domain phi psi rphi rpsi rc theta k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M rphi k ->
 source_l_psiR M phi psi ->source_relativization M domain phi rphi ->source_relativization M domain psi rpsi ->
 schema_renaming M RepC rphi rc ->
 code_relation M(schema_env3 domain rc(zeroM M))(E_L_replacement_theta(CEvar 0)(CEvar 1))theta ->
 source_cutoff_shift M 1 rpsi theta.
Proof.
 intros HD HB HP HR HRS HRC HT.
 destruct(source_cutoff_shift_total M 2 rphi)as(first&HFirst).
 destruct(source_cutoff_shift_total M 2 first)as(second&HSecond).
 pose proof(source_cutoff_two_twice_replacement M rphi first second k HB HFirst HSecond)as HRSecond.
 assert(E:second=rc)by(eapply numerical_renaming_functional;eassumption). subst second.
 exact(source_L_psiR_relative_cutoff M domain phi psi rphi rpsi first rc theta HD HP HR HRS HFirst HSecond HT).
Qed.
Print Assumptions source_L_psiR_Replacement_matrix.

