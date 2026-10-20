(** Actual arbitrary-index use of uniform attempt existence. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceTraceBounds
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceInstantiationConstructors SourceTracePointRules
 SourceRecursionExistsAttempt SourceRecursionExAOn SourceDerivedRules.
Unset Implicit Arguments.
Theorem source_full_rec_exa_on_use M cb cc cn phi o a N out z member exa:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_on M phi o a N out ->sf_relation M SFMember z N member ->source_rec_exa M phi z o a N exa ->
 source_full_prv M cb cc cn out ->source_full_prv M cb cc cn member ->source_full_prv M cb cc cn exa.
Proof.
 intros BP(member0&exa0&point&HM&HA&HP&HAll)HMZ HAZ POut PMember.
 destruct(sf_relation_total M SFImpl member exa)as(result&HR).
 destruct(substitution_singleton_total M z)as(rb&rc&HHead&_).
 assert(HAInst:numerical_instantiation M exa0 z exa).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_exa_substitution M phi(zeroM M)(succM M o)(succM M a)(succM M N)exa0 z o a N exa
   rb rc(code_numeral M 1)(zeroM M)BP HA HAZ HHead(substitution_singleton_tail M rb rc o)(substitution_singleton_tail M rb rc a)(substitution_singleton_tail M rb rc N)). }
 pose proof(source_instantiation_binary M SFImpl member0 exa0 point z member exa result(or_intror(or_intror eq_refl))HP
  (source_instantiation_head_member M N member0 z member HM HMZ)HAInst HR)as HInst.
 pose proof(full_source_AllE M cb cc cn point out z result
  (source_wf_quantifier_instance M cb cc cn SFAll point out z result(or_introl eq_refl)HAll(source_full_prv_wellformed M cb cc cn out POut)HInst)POut HAll HInst)as PResult.
 exact(source_full_modus_ponens M cb cc cn member exa result HR PResult PMember).
Qed.
Print Assumptions source_full_rec_exa_on_use.
