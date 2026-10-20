(** Exact closure-recipe calibration and actual named-to-canonical
    source proof transport for arbitrary internal representation matrices. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceFiniteNameParameters SourceParameterIdentityCalibration SourceDefinabilityPrimitives SourceRepresentationRecipe
 SourceRepresentationClosureRecipe SourceRepresentationFalsityClosure SourceEnvironmentCarrierClosure
 SourceRepresentationNamedWitness SourceRepresentationClosureNormalization SourceRepresentationConjunctionCoordinates
 SourceNamedClosureExistence SourceNamedDifferenceCertificates SourceNamedQuantifierRules
 SourcePropositionalTemplates SourcePropRenaming SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability
 NumericalRenamingMaps NumericalRenaming.
Unset Implicit Arguments.
Local Opaque code_numeral.
Theorem source_representation_closure_graph M count phi rep out:
 source_representation_recipe M count phi rep->source_representation_in_closure_recipe M count phi out->
 source_environment_carrier_closure_statement M rep out.
Proof.
 intros HRep(rep'&succ&closure&body&ex&middle&HR&HS&HC&HB&HE&HM&HO).
 assert(rep'=rep)by(eapply source_representation_recipe_functional;eassumption). subst rep'.
 assert(succ=code_numeral M(sf_encode source_def_successor01)).
 { exact(code_relation_functional M representation_successor_expression(representation_identity_environment M)succ _ HS
   (source_parameter_identity_calibration M source_def_successor01(source_finite_parameter_names 3)(representation_identity_environment M)(representation_identity_names_graph M))). }
 subst succ.
 assert(closure=code_numeral M(sf_encode representation_closure_condition)).
 { exact(code_relation_functional M representation_closure_expression(representation_identity_environment M)closure _ HC
   (source_parameter_identity_calibration M representation_closure_condition(source_finite_parameter_names 3)(representation_identity_environment M)(representation_identity_names_graph M))). }
 subst closure. exact(source_environment_carrier_closure_statement_join M rep body ex middle out HB HE HM HO).
Qed.
Theorem source_zfr_named_representation_closure M rep mt et namedout out:
 source_bounded M rep(code_numeral M 2)->source_environment_carrier_closure_statement M rep out->
 sf_relation M SFAnd(representation_named_member02 M)rep mt->source_named_quantifier M false(zeroM M)mt et->
 code_relation M(named_closure_values M et)(source_prop_expression NCE_template)namedout->source_zfr_provable M namedout->source_zfr_provable M out.
Proof.
 intros BRep HOut HMT HET GNamed PNamed.
 destruct(sf_relation_total M SFAnd(representation_member_code M)rep)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(ex&HE).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode representation_closure_condition))ex)as(middle&HM).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode source_def_successor01))middle)as(result&HO).
 pose proof(source_environment_carrier_closure_statement_join M rep body ex middle result HB HE HM HO)as HJoin.
 rewrite(source_environment_carrier_closure_statement_functional M rep out result HOut HJoin).
 destruct(source_representation_conjunction_coordinates_total M)as(b&c&HOne&HTwo&HSeven&HNS&HNC).
 pose proof(source_named_representation_exists_rename M rep mt et body ex b c(code_numeral M 8)(zeroM M)BRep HMT HET HOne HTwo HB HE)as HETLift.
 set(values:=NCE_values M(code_numeral M(sf_encode source_def_successor01))(code_numeral M(sf_encode representation_closure_condition))ex).
 assert(GResult:code_relation M values(source_prop_expression NCE_template)result).
 { apply(source_prop_template_join M values SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))_ middle result eq_refl);[|exact HO].
   exact(source_prop_template_join M values SFImpl(SPTSlot 1)(SPTSlot 2)_ ex middle eq_refl eq_refl HM). }
 assert(HRename:numerical_renaming M namedout b c(code_numeral M 8)(zeroM M)result).
 { apply(source_prop_renaming M(named_closure_values M et)values b c(code_numeral M 8)(zeroM M)NCE_template namedout result);[|exact GNamed|exact GResult].
   cbn[source_prop_slots NCE_template named_closure_values NCE_values values]. exact(conj HNS(conj HNC HETLift)). }
 apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor namedout b c(code_numeral M 8)(zeroM M)result
  (proj2(source_zfr_descriptor_provable M namedout)PNamed)HRename).
Qed.
Print Assumptions source_representation_closure_graph.
Print Assumptions source_zfr_named_representation_closure.
