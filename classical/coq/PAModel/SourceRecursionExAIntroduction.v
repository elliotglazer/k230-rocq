(** Actual chosen-attempt and chosen-value existential introduction for ExA. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceInstantiationConstructors
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptTransport SourceRecursionAppExists SourceRecursionExistsAttempt.
Unset Implicit Arguments.
Theorem source_rec_exa_body_instantiation M phi z o a N oldAtt oldSome oldBody f att some body:
 source_bounded M phi(code_numeral M 2) ->source_rec_attempt M phi(succM M o)(succM M a)(succM M N)(zeroM M)oldAtt ->
 source_rec_app_exists M(zeroM M)(succM M z)oldSome ->sf_relation M SFAnd oldAtt oldSome oldBody ->source_rec_attempt M phi o a N f att ->
 source_rec_app_exists M f z some ->sf_relation M SFAnd att some body ->numerical_instantiation M oldBody f body.
Proof.
 intros BP HOA HOS HOB HA HS HB. destruct(substitution_singleton_total M f)as(rb&rc&HHead&_).
 assert(IA:numerical_instantiation M oldAtt f att).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_attempt_substitution M phi(succM M o)(succM M a)(succM M N)(zeroM M)oldAtt o a N f att
    rb rc(code_numeral M 1)(zeroM M)BP HOA HA(substitution_singleton_tail M rb rc o)(substitution_singleton_tail M rb rc a)(substitution_singleton_tail M rb rc N)HHead). }
 assert(IS:numerical_instantiation M oldSome f some).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_app_exists_substitution M(zeroM M)(succM M z)oldSome f z some rb rc(code_numeral M 1)(zeroM M)HOS HS HHead(substitution_singleton_tail M rb rc z)). }
 exact(source_instantiation_binary M SFAnd oldAtt oldSome oldBody f att some body(or_introl eq_refl)HOB IA IS HB).
Qed.
Theorem source_full_rec_exa_intro M cb cc cn phi z o a N target f v att app k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M z k ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->context_bounded M cb cc cn k ->
 source_rec_exa M phi z o a N target ->source_rec_attempt M phi o a N f att ->source_rec_app M f z v app ->
 source_full_prv M cb cc cn att ->source_full_prv M cb cc cn app ->source_full_prv M cb cc cn target.
Proof.
 intros BP BZ BO BA BN BF BC HT HA HApp PA PApp.
 pose proof(source_rec_exa_bounded M phi z o a N target k BP BZ BO BA BN HT)as BT.
 destruct(source_rec_app_exists_total M f z)as(some&HS).
 pose proof(source_full_rec_app_exists_intro M cb cc cn f z v app some k BF BZ BC HApp HS PApp)as PSome.
 destruct HT as(oldAtt&oldSome&oldBody&HOA&HOS&HOB&HEx).
 destruct(sf_relation_total M SFAnd att some)as(body&HB).
 pose proof(source_rec_exa_body_instantiation M phi z o a N oldAtt oldSome oldBody f att some body BP HOA HOS HOB HA HS HB)as HI.
 assert(PBody:source_full_prv M cb cc cn body).
 { exact(full_source_CI M cb cc cn att some body(source_wf_binary M cb cc cn SFAnd att some body(or_introl eq_refl)HB
   (source_full_prv_wellformed M cb cc cn att PA)(source_full_prv_wellformed M cb cc cn some PSome))PA PSome HB). }
 exact(full_source_ExI M cb cc cn oldBody target f body(ex_intro _ k(conj BT BC))PBody HEx HI).
Qed.
Print Assumptions source_rec_exa_body_instantiation.
Print Assumptions source_full_rec_exa_intro.
