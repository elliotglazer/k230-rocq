(** Genuine common reflection geometry for both native selectors, with
 all selector codes, PCS tables, validity and inclusions actually generated. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceWitnessThetaRecipe SourceFiniteCutoffShift SourceNativePowerCarrierFixed SourceNativePowerCarrierOld
 SourcePCSTables SourcePieceConjunctionBounds SourceLFixed SourceHierarchySyntax SourceSharedReflectionGeometry
 SourceReflectionGeometryRecipe SourceOrdinalPredicate NumericalInstantiation SourceZFRProvability NumericalContexts ContextCombination.
From Undecidability.FOL Require Import Syntax.Bounded.
From OldZFC Require Z_rel.
Unset Implicit Arguments.
Local Opaque code_numeral.
Theorem source_native_cp_theta_bounded M:
 source_bounded M(code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4).
Proof.
 apply(proj2(source_formula_numeral_bounded M source_native_cp_theta 4)).
 exact(@isolated_bounded OC.falsity_on 4 old_native_cp_theta
  (OldZFC.Z_rel.fb_bounded _ 4 old_native_cp_theta_bound)).
Qed.
Local Transparent code_numeral.
Theorem source_zfr_native_shared_geometry_total M phi n seed:
 source_bounded M phi(succM M(succM M n))->
 exists theta level pb pc pn qb qc qn sb sc pieces ordinal geometry law,
 source_witness_theta_recipe M phi theta /\source_bounded M theta(source_succ_iter M 4 n) /\
 source_LL_instance M(code_numeral M 1)(zeroM M)level /\source_bounded M level(code_numeral M 2) /\
 source_pcs_table M(source_L_domain_code M)theta(source_succ_iter M 4 n)pb pc pn /\
 source_pcs_table M(source_L_domain_code M)(code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4)qb qc qn /\
 context_union M pb pc pn qb qc qn sb sc pieces /\source_piece_table_valid M sb sc pieces /\
 context_included M pb pc pn sb sc pieces /\context_included M qb qc qn sb sc pieces /\
 numerical_instantiation M(source_ordinal_predicate_code M)seed ordinal /\
 source_reflection_geometry_recipe M(source_L_domain_code M)level sb sc pieces seed geometry /\
 sf_relation M SFImpl ordinal geometry law /\source_zfr_provable M law.
Proof.
 intro BP. destruct(source_witness_theta_recipe_total M phi)as(theta&HTheta).
 pose proof(source_witness_theta_recipe_bound M phi theta n BP HTheta)as BTheta.
 destruct(source_LL_instance_total M(code_numeral M 1)(zeroM M))as(level&HLevel).
 assert(BLevel:source_bounded M level(code_numeral M 2)).
 { apply(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2));
   [apply coding_lt_succ|apply coding_zero_lt_succ|exact HLevel]. }
 destruct(source_pcs_table_total M(source_L_domain_code M)theta(source_succ_iter M 4 n))as(pb&pc&pn&HPT).
 destruct(source_pcs_table_total M(source_L_domain_code M)(code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4))as(qb&qc&qn&HQT).
 destruct(source_zfr_shared_reflection_geometry M level theta(source_succ_iter M 4 n)pb pc pn
  (code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4)qb qc qn seed
  HLevel BTheta HPT(source_native_cp_theta_bounded M)HQT)
  as(sb&sc&pieces&ordinal&geometry&law&HU&HV&HPIn&HQIn&HO&HG&HImpl&PLaw).
 exists theta,level,pb,pc,pn,qb,qc,qn,sb,sc,pieces,ordinal,geometry,law.
 repeat first[assumption|split].
Qed.
Print Assumptions source_native_cp_theta_bounded.
Print Assumptions source_zfr_native_shared_geometry_total.
