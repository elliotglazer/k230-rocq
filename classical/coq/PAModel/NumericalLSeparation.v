(** Actual uniform L Separation image for arbitrary internal source matrices and parameter-prefix lengths. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalZFCAxioms NumericalZFCClosure NumericalSetClosure SchemaRenamingDescriptors SchemaRenamingBounds
 SetSchemaConstructors QuotationSchemaSkeleton SourceRelativeSchemaConstructors SourceSchemaRelativization
 SourceRelativization SourceSetRelativization SourcePredicateBlocks SourceLFixed SourceLMatrixRecipes
 SourceD0Recipe SourceLDefinableProfile SourceLSeparationCarrierShell SourceLSeparationWitnessShift SourceCommonReflectedLevel
 SourceCommonReflectedLevelExists SourceLSeparationClosedFromShared SourceZFRProvability SourceKZFCForwardSchemas.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem numerical_L_separation_image M f rf :
 numerical_closed_separation M f ->source_relativization M(source_L_domain_code M)f rf ->source_zfr_provable M rf.
Proof.
 intros [_ [phi [n [HPhi [body [rawopen [HBody [HRaw HClosed]]]]]]]] HImage.
 destruct(source_l_psiS_total M phi)as(psi&HPsi).
 destruct(source_cutoff_shift_thrice_total M phi)as(matrix&HMatrix).
 destruct(source_relativization_total M(source_L_domain_code M)body)as(rp&HRP).
 destruct(source_relativization_total M(source_L_domain_code M)matrix)as(lp&HLP).
 destruct(source_set_relativization_total M(code_numeral M 2)matrix)as(sp&HSP).
 destruct(source_L_definable_profile_total M psi)as(defex&HDef).
 destruct(code_relation_total M(E_L_carrier_reflection(CEvar 0)(CEvar 1))(L_definable_profile_environment lp sp))as(allr&HRef).
 destruct(code_relation_total M(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))(L_definable_profile_environment rp(source_L_domain_code M)))as(witness&HWitness).
 destruct(code_relation_total M(skeleton_relative_code separation_skeleton)
  (skeleton_relative_environment(source_L_domain_code M)(fun _=>rp)))as(target&HTarget).
 assert(HTargetConstructor:sf_relative_separation_constructor M(source_L_domain_code M)rp target)by exact HTarget.
 pose proof(source_separation_constructor_relativization M(source_L_domain_code M)body rp rawopen target HRP HRaw HTargetConstructor)as HOpenImage.
 destruct(source_predicate_block_total M(zeroM M)(source_L_domain_code M)(succM M n))as(block&HBlock).
 destruct(source_common_reflected_level_recipe_total M(zeroM M)(succM M n)(succM M n)phi)as(whole&HWhole).
 destruct(sf_relation_total M SFImpl block whole)as(law&HLaw).
 pose proof(source_zfr_common_reflected_level_exists M(zeroM M)(succM M n)(succM M n)phi block whole law HPhi HBlock HWhole HLaw)as PLaw.
 exact(source_zfr_L_separation_closed_from_shared M phi psi body matrix rp lp sp defex allr witness n rawopen target f rf block whole law
  HPhi HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness HRaw HTargetConstructor HClosed HOpenImage HImage HBlock HWhole HLaw PLaw).
Qed.
Theorem actual_L_separation_images M :L_separation_image_obligation M.
Proof. intros f rf HF HR. exact(numerical_L_separation_image M f rf HF HR). Qed.
Print Assumptions numerical_L_separation_image.
Print Assumptions actual_L_separation_images.
