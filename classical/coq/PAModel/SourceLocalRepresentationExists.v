(** The actual uniform representation proof yields an arbitrary named
    representative inside the chosen closure container. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceRepresentationFalsityClosure
 SourceEnvironmentCarrierClosure SourceParameterIdentityCalibration SourceFiniteNameParameters
 SourceLocalNamedClosureExistence SourceRoleReopening NumericalSubstitution SourceNamedQuantifierRules
 SourceProofWeakening SourceDerivedRules.
Unset Implicit Arguments.
Theorem source_representation_closure_as_environment M count phi rep canonical:
 source_representation_recipe M count phi rep ->source_representation_in_closure_recipe M count phi canonical ->
 source_environment_carrier_closure_statement M rep canonical.
Proof.
 intros HR(r&s&c&body&ex&middle&HR'&HS&HC&HB&HE&HM&HO).
 rewrite(source_representation_recipe_functional M count phi r rep HR' HR)in HB.
 assert(GS:code_relation M(representation_identity_environment M)representation_successor_expression
  (code_numeral M(sf_encode SourceDefinabilityPrimitives.source_def_successor01))).
 { apply source_parameter_identity_calibration. intro i. unfold source_finite_parameter_names.
   destruct(Nat.ltb i 3);reflexivity. }
 assert(GC:code_relation M(representation_identity_environment M)representation_closure_expression
  (code_numeral M(sf_encode representation_closure_condition))).
 { apply source_parameter_identity_calibration. intro i. unfold source_finite_parameter_names.
   destruct(Nat.ltb i 3);reflexivity. }
 rewrite(code_relation_functional M _ _ s _ HS GS)in HO.
 rewrite(code_relation_functional M _ _ c _ HC GC)in HM.
 exact(source_environment_carrier_closure_statement_join M rep body ex middle canonical HB HE HM HO).
Qed.
Theorem source_full_local_representation_exists M fb fc fn gb gc gn count phi rep canonical A S C witness
 rb rc assigned member body ex succ closure k:
 source_bounded M phi count ->source_representation_recipe M count phi rep ->
 source_representation_in_closure_recipe M count phi canonical ->
 context_bounded M fb fc fn(zeroM M) ->source_full_prv M fb fc fn canonical ->
 context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 witness<>A ->witness<>C ->source_role_reopening M A witness rb rc ->
 numerical_substitution M rep rb rc(code_numeral M 2)(code_numeral M 2)assigned ->
 sf_relation M SFMember witness C member ->sf_relation M SFAnd member assigned body ->
 source_named_quantifier M false witness body ex ->
 code_relation M(local_closure_roles A S C)representation_successor_expression succ ->
 code_relation M(local_closure_roles A S C)representation_closure_expression closure ->
 source_full_prv M gb gc gn succ ->source_full_prv M gb gc gn closure ->source_full_prv M gb gc gn ex.
Proof.
 intros BF HR HCanonical BC0 PC0 HIncluded BC WA WC HOpen HAssigned HM HB HE HS HC PS PC.
 destruct(sf_relation_total M SFImpl closure ex)as(middle&HMiddle).
 destruct(sf_relation_total M SFImpl succ middle)as(out&HOut).
 pose proof(source_full_local_named_closure_exists M fb fc fn rep canonical A S C witness rb rc assigned member body ex succ closure middle out
  (source_representation_recipe_bounded M count phi rep BF HR)
  (source_representation_closure_as_environment M count phi rep canonical HR HCanonical)
  BC0 PC0 WA WC HOpen HAssigned HM HB HE HS HC HMiddle HOut)as POut0.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn out k POut0 HIncluded BC)as POut.
 exact(source_full_modus_ponens M gb gc gn closure ex middle HMiddle
  (source_full_modus_ponens M gb gc gn succ middle out HOut POut PS)PC).
Qed.
Print Assumptions source_representation_closure_as_environment.
Print Assumptions source_full_local_representation_exists.
