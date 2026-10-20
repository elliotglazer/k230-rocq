(** Actual existential introduction of a chosen predecessor value. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceInstantiationConstructors
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionBinaryInstance SourceRecursionBinaryGraphTransport
 SourceRecursionAttemptStepShell SourceRecursionValuePairs.
Unset Implicit Arguments.
Theorem source_rec_transition_body_instantiation M phi f u w oldApp oldG oldBody p app binary body:
 source_bounded M phi(code_numeral M 2) ->source_rec_app M(succM M f)(succM M u)(zeroM M)oldApp ->
 source_rec_binary M phi(zeroM M)(succM M w)oldG ->sf_relation M SFAnd oldApp oldG oldBody ->
 source_rec_app M f u p app ->source_rec_binary M phi p w binary ->sf_relation M SFAnd app binary body ->numerical_instantiation M oldBody p body.
Proof.
 intros BP HOldApp HOldG HOldBody HApp HBinary HBody.
 destruct(substitution_singleton_total M p)as(rb&rc&HHead&_).
 assert(IG:numerical_instantiation M oldG p binary).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_binary_substitution_graph M phi(zeroM M)(succM M w)oldG p w binary
    rb rc(code_numeral M 1)(zeroM M)BP HOldG HBinary HHead(substitution_singleton_tail M rb rc w)). }
 exact(source_instantiation_binary M SFAnd oldApp oldG oldBody p app binary body(or_introl eq_refl)HOldBody
  (source_rec_app_instantiation M f u oldApp p app HOldApp HApp)IG HBody).
Qed.
Theorem source_full_rec_transition_intro M cb cc cn phi f u w target p app binary k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M f k ->coding_lt M u k ->coding_lt M w k ->context_bounded M cb cc cn k ->
 source_rec_transition_witness M phi f u w target ->source_rec_app M f u p app ->source_rec_binary M phi p w binary ->
 source_full_prv M cb cc cn app ->source_full_prv M cb cc cn binary ->source_full_prv M cb cc cn target.
Proof.
 intros BP BF BU BW BC HT HA HG PA PG.
 pose proof(source_rec_transition_witness_bounded M phi f u w target k BP BF BU BW HT)as BT.
 destruct HT as(oldApp&oldG&oldBody&HOldApp&HOldG&HOldBody&HEx).
 destruct(sf_relation_total M SFAnd app binary)as(body&HBody).
 pose proof(source_rec_transition_body_instantiation M phi f u w oldApp oldG oldBody p app binary body BP HOldApp HOldG HOldBody HA HG HBody)as HI.
 assert(PBody:source_full_prv M cb cc cn body).
 { exact(full_source_CI M cb cc cn app binary body(source_wf_binary M cb cc cn SFAnd app binary body(or_introl eq_refl)HBody
  (source_full_prv_wellformed M cb cc cn app PA)(source_full_prv_wellformed M cb cc cn binary PG))PA PG HBody). }
 exact(full_source_ExI M cb cc cn oldBody target p body(ex_intro _ k(conj BT BC))PBody HEx HI).
Qed.
Print Assumptions source_rec_transition_body_instantiation.
Print Assumptions source_full_rec_transition_intro.
