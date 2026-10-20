(** A genuine common geometry for two arbitrary internal matrices. Both PCS
    tables are included in one actual internally finite valid union table. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalContexts ContextCombination
 NumericalInstantiation SourceBounded SourcePCSTables SourcePieceConjunctionBounds SourceOrdinalPredicate SourceLFixed
 SourceHierarchySyntax SourceReflectionGeometryRecipe SourceReflectionGeometryTheorem SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_piece_table_valid_union M pb pc pn qb qc qn gb gc gn:
 source_piece_table_valid M pb pc pn ->source_piece_table_valid M qb qc qn ->
 context_union M pb pc pn qb qc qn gb gc gn ->source_piece_table_valid M gb gc gn.
Proof.
 intros HP HQ HU entry count phi HE HPair.
 apply(proj2 HU entry)in HE. destruct HE as[HE|HE];[exact(HP entry count phi HE HPair)|exact(HQ entry count phi HE HPair)].
Qed.
Theorem source_zfr_shared_reflection_geometry M level phi pcount pb pc pn psi qcount qb qc qn seed:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->
 source_bounded M phi pcount ->source_pcs_table M(source_L_domain_code M)phi pcount pb pc pn ->
 source_bounded M psi qcount ->source_pcs_table M(source_L_domain_code M)psi qcount qb qc qn ->
 exists gb gc gn ordinal geometry law,
 context_union M pb pc pn qb qc qn gb gc gn /\source_piece_table_valid M gb gc gn /\
 context_included M pb pc pn gb gc gn /\context_included M qb qc qn gb gc gn /\
 numerical_instantiation M(source_ordinal_predicate_code M)seed ordinal /\
 source_reflection_geometry_recipe M(source_L_domain_code M)level gb gc gn seed geometry /\
 sf_relation M SFImpl ordinal geometry law /\source_zfr_provable M law.
Proof.
 intros HL HP HPT HQ HQT.
 pose proof(source_pcs_table_valid M(source_L_domain_code M)phi pcount pb pc pn(numerical_L_domain_bounded M)HP HPT)as HVP.
 pose proof(source_pcs_table_valid M(source_L_domain_code M)psi qcount qb qc qn(numerical_L_domain_bounded M)HQ HQT)as HVQ.
 destruct(context_union_total M pb pc pn qb qc qn)as(gb&gc&gn&HU).
 pose proof(source_piece_table_valid_union M pb pc pn qb qc qn gb gc gn HVP HVQ HU)as HV.
 destruct(source_zfr_reflection_geometry_total M level gb gc gn seed HL HV)as(ordinal&geometry&law&HO&HG&HImpl&PLaw).
 exists gb,gc,gn,ordinal,geometry,law. split;[exact HU|]. split;[exact HV|].
 split;[exact(context_union_left M pb pc pn qb qc qn gb gc gn HU)|].
 split;[exact(context_union_right M pb pc pn qb qc qn gb gc gn HU)|].
 split;[exact HO|]. split;[exact HG|]. split;assumption.
Qed.
Print Assumptions source_piece_table_valid_union.
Print Assumptions source_zfr_shared_reflection_geometry.
