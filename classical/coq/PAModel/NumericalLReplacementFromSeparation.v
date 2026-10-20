(** Actual uniform L Replacement image from the exact L Separation image.
    Every matrix/count ranges over the arbitrary PA model. Raw guarded
    Replacement, L-bounding and all syntax/proof transformations are proved
    dependencies; the sole hypothesis is the stated Separation family. *)
From Stdlib Require Import List.
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SetSchemaConstructors SchemaConstructorBounds
 NumericalZFCAxioms NumericalZFCClosure NumericalSetClosure SchemaRenamingDescriptors SchemaRenamingBounds
 SourceKZFCForwardSchemas SourceLFixed SourceLMatrixRecipes SourceRelativization SourceRelativizationBounds SourceSchemaRelativization
 SourceRelativeSchemaInputs SourceRelativeSchemaConstructors QuotationSchemaSkeleton SourceDomainContexts SourceGuardedDomainClosure
 SourceLSeparationUseFromImages SourceLReplacementPsiR SourceLReplacementMatrix SourceLReplacementCutShells SourceLReplacementBoundCut
 SourceLReplacementShellRebase SourceLReplacementAllocation SourceLReplacementOpen SourceLElementBoundShell
 SourceFiniteCutoffShift SourceQfFunctionality SourceZFRReplacementUse SourceZFRProvability SourceSetTheoryDescriptors
 SourceDescriptorProvability SourceFiniteProofContexts SourceAxiomContexts NumericalContexts NumericalSourceFull ContextCombination NumericalRenaming SourceQuantifierRules.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem numerical_L_replacement_image_from_separation M:
 L_separation_image_obligation M ->forall f rf,numerical_closed_replacement M f ->
 source_relativization M(source_L_domain_code M)f rf ->source_zfr_provable M rf.
Proof.
 intros HS f rf [_ [phi [count [HPhi [bodyA [bodyB [bodyC [open [HBodyA [HBodyB [HBodyC [HOpen HClosed]]]]]]]]]]]] HImage.
 set(domain:=source_L_domain_code M).
 pose proof(numerical_L_domain_bounded M)as HD. change(source_bounded M domain(code_numeral M 1))in HD.
 destruct(source_relativization_total M domain phi)as(rphi&HRPhi).
 pose proof(source_relativization_preserves_bound M phi domain(succM M(succM M count))rphi HD HPhi HRPhi)as BRPhi.
 destruct(relative_replacement_matrix_total M domain rphi)as(matrix&HMatrix).
 pose proof(relative_replacement_matrix_bound M domain rphi matrix count HD BRPhi HMatrix)as BMatrix.
 destruct(source_zfr_replacement_open_total M matrix count BMatrix)as(ma&mb&mc&raw&HMA&HMB&HMC&HRaw&PRaw).
 destruct(schema_renaming_total M RepA rphi)as(ra&HRA).
 destruct(schema_renaming_total M RepB rphi)as(rb&HRB).
 destruct(schema_renaming_total M RepC rphi)as(rc&HRC).
 destruct(code_relation_total M(skeleton_relative_code replacement_skeleton)
   (skeleton_relative_environment domain(schema_env3 ra rb rc)))as(target&HTarget).
 assert(HTarget':sf_relative_replacement_constructor M domain ra rb rc target)by exact HTarget.
 pose proof(source_relativization_schema_renaming M domain phi rphi RepA bodyA ra HD HRPhi HBodyA HRA)as HRelA.
 pose proof(source_relativization_schema_renaming M domain phi rphi RepB bodyB rb HD HRPhi HBodyB HRB)as HRelB.
 pose proof(source_relativization_schema_renaming M domain phi rphi RepC bodyC rc HD HRPhi HBodyC HRC)as HRelC.
 pose proof(source_replacement_constructor_relativization M domain bodyA bodyB bodyC ra rb rc open target
  HRelA HRelB HRelC HOpen HTarget')as HOpenRel.
 destruct(numerical_renaming_total M domain(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(domain1&HDShift).
 destruct(code_relation_total M(E_L_replacement_theta(CEvar 0)(CEvar 1))(schema_env3 domain rc(zeroM M)))as(theta&HTheta).
 destruct(source_l_psiR_total M phi)as(psi&HPsi).
 pose proof(source_l_psiR_bounded M phi psi count HPhi HPsi)as BPsi.
 destruct(source_relativization_total M domain psi)as(rpsi&HRPsi).
 pose proof(source_relativization_preserves_bound M psi domain(succM M(succM M count))rpsi HD BPsi HRPsi)as BRPsi.
 pose proof(source_L_psiR_Replacement_matrix M domain phi psi rphi rpsi rc theta(succM M(succM M count))
   HD BRPhi HPsi HRPhi HRPsi HRC HTheta)as HThetaCutoff.
 destruct(source_cutoff_shift_total M 2 theta)as(first&HFirst).
 destruct(source_cutoff_shift_total M 3 first)as(second&HSecond).
 destruct(source_L_replacement_cutoff_slots M rpsi theta first second count BRPsi HThetaCutoff HFirst HSecond)
  as(BTheta&BFirst&BSecond&HFirst1&HSecond1&HSecond2&HRelSepBody).
 destruct(schema_renaming_total M SepBody psi)as(sepBody&HSepBody).
 destruct(sf_separation_constructor_total M sepBody)as(sepRaw&HSepRaw).
 destruct(code_relation_total M(E_L_separation_law(CEvar 0)(CEvar 1))(schema_env3 domain first(zeroM M)))as(separation&HSepGraph).
 pose proof(proj2(source_L_separation_law_rebase M domain first separation)HSepGraph)as HRelativeSep.
 pose proof(source_relativization_schema_renaming M domain psi rpsi SepBody sepBody first HD HRPsi HSepBody HRelSepBody)as HSepBodyRel.
 pose proof(source_separation_constructor_relativization M domain sepBody first sepRaw separation HSepBodyRel HSepRaw HRelativeSep)as HSepRel.
 destruct(source_zfr_L_separation_instance_from_images M psi(succM M count)sepBody sepRaw separation
  HS BPsi HSepBody HSepRaw HSepRel)as(sepClosed&sepImage&HSepClosed&HRelClosed&PSep).
 destruct(code_relation_total M(E_L_separation_law(CEvar 0)(CEvar 1))(schema_env3 domain second(zeroM M)))as(shiftedSeparation&HShiftSep).
 destruct(source_zfr_L_element_bound_shell M)as(bound&HBound&PBound).
 assert(Premises:forall x,In x[raw;bound;sepImage] ->source_descriptor_provable M ZFRSourceDescriptor x).
 { intros x[<-|[<-|[<-|[]]]];apply(proj2(source_zfr_descriptor_provable M _));assumption. }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor[raw;bound;sepImage]Premises)
  as(gb&gc&gn&HBase&PBase).
 pose proof(proj1(source_zfr_descriptor_context M gb gc gn)HBase)as HZFR.
 destruct(source_domain_context_total M domain count)as(db&dc&HTable).
 destruct(context_union_total M gb gc gn db dc count)as(b&c&l&HUnion).
 pose proof(source_full_L_replacement_open_from_certificates M domain domain1 rphi matrix ra rb rc ma mb mc raw
   theta first second bound sepRaw sepClosed sepImage separation shiftedSeparation target
   gb gc gn db dc b c l count
   HD HDShift BRPhi HMatrix HRA HRB HRC HMA HMB HMC HRaw HTarget' HTheta
   BTheta BFirst BSecond HFirst1 HFirst HSecond1 HSecond2 HSecond HBound HSepGraph HShiftSep
   (schema_separation_constructor_bound M sepBody sepRaw(succM M count)
     (schema_separation_bound M psi sepBody(succM M count)BPsi HSepBody)HSepRaw)
   HSepClosed HSepRel HRelClosed(proj1 HBase)HTable HUnion
   (PBase raw(or_introl eq_refl))(PBase bound(or_intror(or_introl eq_refl)))
   (PBase sepImage(or_intror(or_intror(or_introl eq_refl)))))as PTarget.
 exists gb,gc,gn. split;[exact HZFR|].
 exact(source_full_guarded_domain_close M domain gb gc gn(proj1 HBase)HD count open target f rf db dc b c l
   (schema_replacement_constructor_bound M bodyA bodyB bodyC open count
    (schema_replacement_a_bound M phi bodyA count HPhi HBodyA)
    (schema_replacement_b_bound M phi bodyB count HPhi HBodyB)
    (schema_replacement_c_bound M phi bodyC count HPhi HBodyC)HOpen)
    HClosed HOpenRel HImage HTable HUnion PTarget).
Qed.
Theorem L_replacement_images_from_separation M:
 L_separation_image_obligation M ->L_replacement_image_obligation M.
Proof. exact(numerical_L_replacement_image_from_separation M). Qed.
Print Assumptions numerical_L_replacement_image_from_separation.
Print Assumptions L_replacement_images_from_separation.
