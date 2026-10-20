(** Bounds and exact shared-guard reopening for a supplied recipe row. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceRenamingBounds NumericalRenamingMaps NumericalRenaming SourceSetRelativization SourceSetRelativizationBounds
 SourceSetRelativizationFunctionality SourceRepresentationRecipe SourceRepresentationNamedRecipe SourceRepresentationNamedPoint
 SourceDefinabilityBounds SourceDefinabilityIteration SourceFiniteCutoffShift SourceQfFunctionality
 SourceRepresentativeRenaming SourceDn SetSchemaConstructors.
Unset Implicit Arguments.
Theorem source_representation_relative_bound M count phi matrix relative :
 source_bounded M phi count ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 source_bounded M relative(succM M(succM M(succM M count))).
Proof.
 intros HP HM HR. assert(BM:source_bounded M matrix(succM M(succM M(succM M count)))).
 { apply(numerical_renaming_preserves_bound M phi _ _ _ _ matrix count _ HP HM).
   intros i j HI HJ. apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)i j(coding_not_lt_zero M i))in HJ.
   subst j. rewrite Arithmetic.add_comm. change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M))))i)
     (succM M(succM M(succM M count)))). rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
   do 3 apply coding_lt_succ_cancel. exact HI. }
 apply(source_set_relativization_preserves_bound M matrix(code_numeral M 2) _ relative);try assumption.
 do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
Qed.
Theorem source_representation_point_reopen M count phi environment first shifted matrix relative point result r renamed :
 source_bounded M phi count ->source_envf M count environment ->
 source_cutoff_shift M 1 environment first ->source_cutoff_shift M 1 first shifted ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 code_relation M(representation_point_environment shifted relative)(E_representation_point(CEvar 0)(CEvar 1))point ->
 source_dn M count point result ->~coding_lt M r(code_numeral M 2) ->source_representative_renaming M r result renamed ->
 exists named,code_relation M(schema_env3 shifted relative(succM M(addM M r count)))E_representation_named_point named /\
 source_dn M count named renamed.
Proof.
 intros HP HE H1 H2 HM HR HB HD HName HResult.
 assert(HRecipe:source_representation_recipe M count phi result).
 { exists environment,first,shifted,matrix,relative,point. exact(conj HE(conj H1(conj H2(conj HM(conj HR(conj HB HD)))))). }
 destruct(source_representation_named_recipe M count phi result r renamed HP HRecipe HName HResult)
  as(e&a&b&m&rel&named&HE'&H1'&H2'&HM'&HR'&HB'&HD').
 assert(E:e=environment)by(eapply source_def_iteration_functional;eassumption). subst e.
 assert(E:a=first)by(eapply source_cutoff_shift_functional;eassumption). subst a.
 assert(E:b=shifted)by(eapply source_cutoff_shift_functional;eassumption). subst b.
 assert(E:m=matrix)by(eapply numerical_renaming_functional;eassumption). subst m.
 assert(E:rel=relative)by(eapply source_set_relativization_functional;eassumption). subst rel.
 exists named. exact(conj HB' HD').
Qed.
Print Assumptions source_representation_relative_bound.
Print Assumptions source_representation_point_reopen.
