(** Actual arbitrary-index elimination of the universal attempt agreement law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalContexts NumericalSourceFull SourceTraceBounds
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceInstantiationConstructors SourceTracePointRules
 SourceRecursionPrimitiveRelations SourceRecursionAgreement SourceRecursionAgreementOn SourceDerivedRules.
Unset Implicit Arguments.
Theorem source_full_rec_agrees_on_use M cb cc cn f g N out z member agreement:
 source_rec_agrees_on M f g N out ->sf_relation M SFMember z N member ->source_rec_agreement M f g z agreement ->
 source_full_prv M cb cc cn out ->source_full_prv M cb cc cn member ->source_full_prv M cb cc cn agreement.
Proof.
 intros(member0&agr0&point&HM&HA&HP&HAll)HMZ HAZ POut PMember.
 destruct(sf_relation_total M SFImpl member agreement)as(result&HR).
 destruct(substitution_singleton_total M z)as(rb&rc&HHead&_).
 assert(HAInst:numerical_instantiation M agr0 z agreement).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_agreement_substitution M(succM M f)(succM M g)(zeroM M)agr0 f g z agreement rb rc(code_numeral M 1)(zeroM M)HA HAZ
   (substitution_singleton_tail M rb rc f)(substitution_singleton_tail M rb rc g)HHead). }
 pose proof(source_instantiation_binary M SFImpl member0 agr0 point z member agreement result(or_intror(or_intror eq_refl))HP
  (source_instantiation_head_member M N member0 z member HM HMZ)HAInst HR)as HInst.
 pose proof(full_source_AllE M cb cc cn point out z result
  (source_wf_quantifier_instance M cb cc cn SFAll point out z result(or_introl eq_refl)HAll(source_full_prv_wellformed M cb cc cn out POut)HInst)POut HAll HInst)as PResult.
 exact(source_full_modus_ponens M cb cc cn member agreement result HR PResult PMember).
Qed.
Print Assumptions source_full_rec_agrees_on_use.
