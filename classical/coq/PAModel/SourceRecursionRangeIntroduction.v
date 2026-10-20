(** Genuine source ExI for a chosen attempt and literal RR. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceInstantiationConstructors
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionAttempt SourceRecursionAttemptTransport SourceRecursionAttemptApp SourceRecursionRangeRelation.
Unset Implicit Arguments.
Theorem source_full_rec_attempt_app_intro M cb cc cn phi z v o a N target f att app k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M z k ->coding_lt M v k ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->context_bounded M cb cc cn k ->
 source_rec_attempt_app M phi z v o a N target ->source_rec_attempt M phi o a N f att ->source_rec_app M f z v app ->
 source_full_prv M cb cc cn att ->source_full_prv M cb cc cn app ->source_full_prv M cb cc cn target.
Proof.
 intros BP BZ BV BO BA BN BC HT HA HApp PA PApp.
 pose proof(source_rec_attempt_app_bounded M phi z v o a N target k BP BZ BV BO BA BN HT)as BT.
 destruct HT as(oldAtt&oldApp&oldBody&HOA&HOApp&HOB&HEx).
 destruct(sf_relation_total M SFAnd att app)as(body&HB).
 destruct(substitution_singleton_total M f)as(rb&rc&HHead&_).
 assert(IA:numerical_instantiation M oldAtt f att).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_attempt_substitution M phi(succM M o)(succM M a)(succM M N)(zeroM M)oldAtt o a N f att
    rb rc(code_numeral M 1)(zeroM M)BP HOA HA(substitution_singleton_tail M rb rc o)(substitution_singleton_tail M rb rc a)(substitution_singleton_tail M rb rc N)HHead). }
 assert(IApp:numerical_instantiation M oldApp f app).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_app_substitution M(zeroM M)(succM M z)(succM M v)oldApp f z v app
    rb rc(code_numeral M 1)(zeroM M)HOApp HApp HHead(substitution_singleton_tail M rb rc z)(substitution_singleton_tail M rb rc v)). }
 pose proof(source_instantiation_binary M SFAnd oldAtt oldApp oldBody f att app body(or_introl eq_refl)HOB IA IApp HB)as HI.
 assert(PBody:source_full_prv M cb cc cn body).
 { exact(full_source_CI M cb cc cn att app body(source_wf_binary M cb cc cn SFAnd att app body(or_introl eq_refl)HB
   (source_full_prv_wellformed M cb cc cn att PA)(source_full_prv_wellformed M cb cc cn app PApp))PA PApp HB). }
 exact(full_source_ExI M cb cc cn oldBody target f body(ex_intro _ k(conj BT BC))PBody HEx HI).
Qed.
Theorem source_full_rec_rr_intro M cb cc cn phi z v o a N target f member att app k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M z k ->coding_lt M v k ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->context_bounded M cb cc cn k ->
 source_rec_rr M phi z v o a N target ->sf_relation M SFMember z N member ->source_rec_attempt M phi o a N f att ->source_rec_app M f z v app ->
 source_full_prv M cb cc cn member ->source_full_prv M cb cc cn att ->source_full_prv M cb cc cn app ->source_full_prv M cb cc cn target.
Proof.
 intros BP BZ BV BO BA BN BC HT HM HA HApp PM PA PApp.
 destruct HT as(member'&witness&HM'&HW&HAnd).
 pose proof(sf_relation_functional M SFMember z N member' member HM' HM)as E. subst member'.
 pose proof(source_full_rec_attempt_app_intro M cb cc cn phi z v o a N witness f att app k BP BZ BV BO BA BN BC HW HA HApp PA PApp)as PW.
 exact(full_source_CI M cb cc cn member witness target(source_wf_binary M cb cc cn SFAnd member witness target(or_introl eq_refl)HAnd
  (source_full_prv_wellformed M cb cc cn member PM)(source_full_prv_wellformed M cb cc cn witness PW))PM PW HAnd).
Qed.
Print Assumptions source_full_rec_attempt_app_intro.
Print Assumptions source_full_rec_rr_intro.
