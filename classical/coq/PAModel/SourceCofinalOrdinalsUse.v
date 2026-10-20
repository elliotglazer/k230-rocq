(** Actual Ordinals(K) plus w-in-K gives the literal Ord(w) proof. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes NumericalSourceFull NumericalInstantiation
 SourceInstantiationConstructors SourceDerivedRules SourceTracePointRules SourceOrdinalPredicate
 SourceCofinalGeometry SourceCofinalOrdinalsShell.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_full_cofinal_ordinals_use M K w ordinals member ordinal b c n:
 source_cofinal_ordinals M K ordinals ->sf_relation M SFMember w K member ->
 numerical_instantiation M(source_ordinal_predicate_code M)w ordinal ->
 source_full_prv M b c n ordinals ->source_full_prv M b c n member ->source_full_prv M b c n ordinal.
Proof.
 intros HO HM HI PO PM.
 destruct(source_cofinal_ordinals_shell M K ordinals HO)as(guard&point&HG&HP&HA).
 destruct(sf_relation_total M SFImpl member ordinal)as(instance&HInstance).
 pose proof(source_instantiation_binary M SFImpl guard(source_ordinal_predicate_code M)point w member ordinal instance
  (or_intror(or_intror eq_refl))HP(source_instantiation_head_member M K guard w member HG HM)HI HInstance)as HInst.
 pose proof(full_source_AllE M b c n point ordinals w instance
  (source_wf_quantifier_instance M b c n SFAll point ordinals w instance(or_introl eq_refl)HA
   (source_full_prv_wellformed M b c n ordinals PO)HInst)PO HA HInst)as PInstance.
 exact(source_full_modus_ponens M b c n member ordinal instance HInstance PInstance PM).
Qed.
Print Assumptions source_full_cofinal_ordinals_use.
