(** Bound of the actual unprefixed representation point. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
 SourceBounded SourceRepresentationRecipe SourceDefinabilityBounds SourceFiniteCutoffShift SourceQfFunctionality
 NumericalRenamingMaps NumericalRenaming SourceRenamingBounds SourceSetRelativization SourceSetRelativizationBounds SchemaConstructorBounds.
Unset Implicit Arguments.
Theorem source_representation_point_data_bound M n phi e a b m r s:
 source_bounded M phi n ->source_envf M n e ->source_cutoff_shift M 1 e a ->source_cutoff_shift M 1 a b ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)m ->
 source_set_relativization M(code_numeral M 2)m r ->
 code_relation M(representation_point_environment b r)(E_representation_point(CEvar 0)(CEvar 1))s ->
 source_bounded M s(succM M(succM M n)).
Proof.
 intros HP HE H1 H2 HM HR HS.
 pose proof(source_cutoff_shift_bounded M 1 e a n(source_envf_bound M n e HE) H1)as BA.
 pose proof(source_cutoff_shift_bounded M 1 a b(succM M n) BA H2)as BB.
 assert(BM:source_bounded M m(succM M(succM M(succM M n)))).
 { apply(numerical_renaming_preserves_bound M phi _ _ _ _ m n _ HP HM).
   intros i j HI HJ. apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)
     (code_numeral M 3) i j(coding_not_lt_zero M i)) in HJ. subst j.
   rewrite Arithmetic.add_comm. change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M)))) i)
     (succM M(succM M(succM M n)))).
   rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
   do 3 apply coding_lt_succ_cancel. exact HI. }
 assert(BR:source_bounded M r(succM M(succM M(succM M n)))).
 { apply(source_set_relativization_preserves_bound M m(code_numeral M 2) _ r);try assumption.
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BS:source_bounded M s(succM M(succM M n))).
 { assert(B: schema_expression_bound M(representation_point_environment b r)
     (E_representation_point(CEvar 0)(CEvar 1))(succM M(succM M n))).
   { unfold E_representation_point,E_sf_iff.
     repeat schema_constructor_bound;try schema_small_index;assumption. }
   exact(B s HS). }
 exact BS.
Qed.
Print Assumptions source_representation_point_data_bound.
