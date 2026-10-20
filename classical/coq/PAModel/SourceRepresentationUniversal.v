(** Complete canonical universal representation existence, via actual
    guarded classical duality and actual implication/Ex constructions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceRepresentationClosureTransport SourceRepresentationUniversalDual
 SourceRepresentationExistential SourceRepresentationImplication SourceZFRFalsityRepresentation SourceEnvironmentCarrierClosureMap
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_representation_universal M count f universal out:
 source_bounded M universal count->sf_relation M SFAll f(zeroM M)universal->
 (forall child,source_representation_in_closure_recipe M(succM M count)f child->source_zfr_provable M child)->
 source_representation_in_closure_recipe M count universal out->source_zfr_provable M out.
Proof.
 intros BAll HAll IH HOut.
 destruct(source_representation_recipe_total M count universal)as(rep&HRep).
 destruct(source_zfr_representation_universal_dual M count f universal rep BAll HAll HRep)
  as(negf&exneg&negative&negativeRep&law&HNegF&HExNeg&HNegative&BNegative&HNegativeRep&HLaw&PLaw).
 pose proof(proj1(proj1(source_bounded_accept_binary M SFImpl exneg(zeroM M)negative count(or_intror(or_intror eq_refl))HNegative)BNegative))as BExNeg.
 pose proof(proj1(source_bounded_accept_unary M SFEx negf exneg count(or_intror eq_refl)HExNeg)BExNeg)as BNegF.
 assert(IHNegF:forall child,source_representation_in_closure_recipe M(succM M count)negf child->source_zfr_provable M child).
 { intros child HChild. exact(source_zfr_representation_implication M(succM M count)f(zeroM M)negf child BNegF HNegF IH
   (fun r HR=>source_zfr_falsity_representation M(succM M count)r HR)HChild). }
 assert(IHExNeg:forall child,source_representation_in_closure_recipe M count exneg child->source_zfr_provable M child).
 { intros child HChild. exact(source_zfr_representation_existential M count negf exneg child BExNeg HExNeg IHNegF HChild). }
 destruct(source_representation_in_closure_recipe_total M count negative)as(negativeOut&HNegativeOut).
 pose proof(source_zfr_representation_implication M count exneg(zeroM M)negative negativeOut BNegative HNegative IHExNeg
  (fun r HR=>source_zfr_falsity_representation M count r HR)HNegativeOut)as PNegative.
 exact(source_zfr_environment_carrier_closure_map M negativeRep rep negativeOut out law
  (source_representation_recipe_bounded M count negative negativeRep BNegative HNegativeRep)
  (source_representation_recipe_bounded M count universal rep BAll HRep)
  (source_representation_closure_graph M count negative negativeRep negativeOut HNegativeRep HNegativeOut)
  (source_representation_closure_graph M count universal rep out HRep HOut)HLaw
  (proj2(source_zfr_descriptor_provable M law)PLaw)PNegative).
Qed.
Print Assumptions source_zfr_representation_universal.
