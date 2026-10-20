(** The actual three-universal functionality accessor for a binary matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull SourceTraceBounds NumericalSubstitutionMaps NumericalSubstitution
 SourceRecursionBinaryInstance SourceRecursionBinaryTransport SchemaRenamingDescriptors SetSchemaConstructors SourceFunctionalityShells
 SourceTripleSpecialization SourceDerivedRules SourceFiniteCutoffShift.
Unset Implicit Arguments.
Definition source_rec_functionality M phi functionality:=exists a b,
 schema_renaming M RepA phi a /\schema_renaming M RepB phi b /\source_functionality_graph M a b functionality.
Theorem source_rec_functionality_total M phi:exists out,source_rec_functionality M phi out.
Proof.
 destruct(schema_renaming_total M RepA phi)as(a&HA).
 destruct(schema_renaming_total M RepB phi)as(b&HB).
 destruct(code_relation_total M (E_sf_functionality(CEvar 0)(CEvar 1)) (schema_env3 a b(zeroM M)))as(out&HO).
 exists out,a,b. repeat split;assumption.
Qed.
Theorem source_full_rec_functionality_use M cb cc cn phi functionality u v w before after equal:
 source_bounded M phi(code_numeral M 2) ->source_rec_functionality M phi functionality ->
 source_rec_binary M phi u v before ->source_rec_binary M phi u w after ->sf_relation M SFEqual v w equal ->
 source_full_prv M cb cc cn functionality ->source_full_prv M cb cc cn before ->source_full_prv M cb cc cn after ->
 source_full_prv M cb cc cn equal.
Proof.
 intros BP(a&b&HA&HB&HF)HBefore HAfter HEqual PF PBefore PAfter.
 pose proof(source_rec_binary_rep M phi a RepA(or_introl eq_refl)BP HA)as HBA.
 pose proof(source_rec_binary_rep M phi b RepB(or_intror eq_refl)BP HB)as HBB.
 destruct(sf_relation_total M SFEqual(code_numeral M 1)(zeroM M))as(rawEqual&HRawEqual).
 destruct(source_functionality_shell M a b rawEqual functionality HRawEqual HF)
  as(rhs&point&p1&p2&HRight&HPoint&HAll1&HAll2&HAll3).
 destruct(source_triple_prefix_total M w v u)as(tb&tc&HT).
 destruct(numerical_substitution_total M a tb tc(code_numeral M 3)(zeroM M))as(a'&HSA).
 destruct(numerical_substitution_total M b tb tc(code_numeral M 3)(zeroM M))as(b'&HSB).
 pose proof(source_rec_binary_substitution M phi(code_numeral M 2)(code_numeral M 1)a tb tc(code_numeral M 3)(zeroM M)a' u v
  BP HBA HSA(proj2(proj2 HT))(proj1(proj2 HT)))as HBA'.
 pose proof(source_rec_binary_substitution M phi(code_numeral M 2)(zeroM M)b tb tc(code_numeral M 3)(zeroM M)b' u w
  BP HBB HSB(proj2(proj2 HT))(proj1 HT))as HBB'.
 pose proof(source_rec_binary_functional M phi u v a' before HBA' HBefore)as EA.
 pose proof(source_rec_binary_functional M phi u w b' after HBB' HAfter)as EB.
 subst a' b'.
 assert(HSE:numerical_substitution M rawEqual tb tc(code_numeral M 3)(zeroM M)equal).
 { apply(proj2(numerical_substitution_equal M _ _ rawEqual tb tc(code_numeral M 3)(zeroM M)equal HRawEqual)).
   exists v,w. repeat split;[exact(proj1(proj2 HT))|exact(proj1 HT)|exact HEqual]. }
 destruct(sf_relation_total M SFImpl after equal)as(targetRight&HTRight).
 destruct(sf_relation_total M SFImpl before targetRight)as(target&HTarget).
 assert(HSR:numerical_substitution M rhs tb tc(code_numeral M 3)(zeroM M)targetRight).
 { apply(proj2(numerical_substitution_binary M SFImpl b rawEqual rhs tb tc(code_numeral M 3)(zeroM M)targetRight
    (or_intror(or_intror eq_refl))HRight)). exists after,equal. repeat split;assumption. }
 assert(HSP:numerical_substitution M point tb tc(code_numeral M 3)(zeroM M)target).
 { apply(proj2(numerical_substitution_binary M SFImpl a rhs point tb tc(code_numeral M 3)(zeroM M)target
    (or_intror(or_intror eq_refl))HPoint)). exists before,targetRight. repeat split;assumption. }
 destruct(source_full_prv_wellformed M cb cc cn functionality PF)as(k&BF&BC).
 pose proof(proj1(source_bounded_accept_unary M SFAll p2 functionality k(or_introl eq_refl)HAll3)BF)as B2.
 pose proof(proj1(source_bounded_accept_unary M SFAll p1 p2(succM M k)(or_introl eq_refl)HAll2)B2)as B1.
 pose proof(proj1(source_bounded_accept_unary M SFAll point p1(succM M(succM M k))(or_introl eq_refl)HAll1)B1)as BPoint.
 pose proof(source_full_triple_specialize M cb cc cn point p1 p2 functionality u v w tb tc target(source_succ_iter M 3 k)
  BPoint HAll1 HAll2 HAll3 HT HSP PF)as PTarget.
 pose proof(source_full_modus_ponens M cb cc cn before targetRight target HTarget PTarget PBefore)as PRight.
 exact(source_full_modus_ponens M cb cc cn after equal targetRight HTRight PRight PAfter).
Qed.
Print Assumptions source_rec_functionality_total.
Print Assumptions source_full_rec_functionality_use.
