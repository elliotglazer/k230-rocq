(** Actual substitution/shift of the complete reflection geometry payload. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceOrdinalPredicate SourceUnarySubstitution SourceReflectionGeometryPoint SourceReflectionGeometryTransport
 SourceReflectionKFTransport SourcePieceConjunctionBounds SourceRecursionPrimitiveRelations SourceRecursionShiftGraphs SourcePropositionalSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_reflection_geometry_point_substitution M domain level sb sc count a K beta old a' K' beta' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_point M domain level sb sc count a K beta old ->source_reflection_geometry_point M domain level sb sc count a' K' beta' new ->
 substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base K K' ->substitution_lookup M rb rc rn base beta beta' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HL HV(m&o&kf&u&ob&l&mb&s&HM&HO&HKF&HU&HOB&HLg&HMB&HS&HOld)
 (m'&o'&kf'&u'&ob'&l'&mb'&s'&HM'&HO'&HKF'&HU'&HOB'&HLg'&HMB'&HS'&HNew)HA HK HB.
 assert(SM:numerical_substitution M m rb rc rn base m').
 { apply(proj2(numerical_substitution_member M a K m rb rc rn base m' HM)). exists a',K'. auto. }
 pose proof(source_cofinal_ordinals_substitution M K o K' o' rb rc rn base HO HO' HK)as SO.
 pose proof(source_reflection_KF_substitution M domain level sb sc count K kf K' kf' rb rc rn base HD HL HV HKF HKF' HK)as SKF.
 assert(Names:forall i,(i<2)%nat ->substitution_lookup M rb rc rn base(source_rec_env2 K beta i)(source_rec_env2 K' beta' i)).
 { intros[|i]HI;[exact HK|exact HB]. }
 pose proof(source_reflection_geometry_substitution M SourceReflectionGeometryPredicates.ReflectionUnion(source_rec_env2 K beta)(source_rec_env2 K' beta')u u' rb rc rn base HU HU' Names)as SU.
 pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)beta ob rb rc rn base beta' ob'(source_ordinal_predicate_bounded M)HOB HB HOB')as SOB.
 pose proof(source_reflection_geometry_substitution M SourceReflectionGeometryPredicates.ReflectionLimit(fun _=>beta)(fun _=>beta')l l' rb rc rn base HLg HLg' ltac:(intros i HI;exact HB))as SL.
 assert(SMB:numerical_substitution M mb rb rc rn base mb').
 { apply(proj2(numerical_substitution_member M a beta mb rb rc rn base mb' HMB)). exists a',beta'. auto. }
 pose proof(source_reflection_geometry_substitution M SourceReflectionGeometryPredicates.ReflectionSubsets(source_rec_env2 K beta)(source_rec_env2 K' beta')s s' rb rc rn base HS HS' Names)as SS.
 apply(source_prop_expression_substitution M(source_reflection_geometry_values m o kf u ob l mb s)(source_reflection_geometry_values m' o' kf' u' ob' l' mb' s')rb rc rn base source_reflection_geometry_payload);[|exact HOld|exact HNew].
 intros[|[|[|[|[|[|[|i]]]]]]];cbn[source_reflection_geometry_values];assumption.
Qed.
Theorem source_reflection_geometry_point_shift M domain level sb sc count a K beta old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_geometry_point M domain level sb sc count a K beta old ->
 source_reflection_geometry_point M domain level sb sc count(succM M a)(succM M K)(succM M beta)new ->source_formula_shift M old new.
Proof.
 intros HD HL HV HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_reflection_geometry_point_substitution M domain level sb sc count a K beta old(succM M a)(succM M K)(succM M beta)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HL HV HO HN(source_rec_shift_lookup M a)(source_rec_shift_lookup M K)(source_rec_shift_lookup M beta)).
Qed.
Print Assumptions source_reflection_geometry_point_substitution.
Print Assumptions source_reflection_geometry_point_shift.
