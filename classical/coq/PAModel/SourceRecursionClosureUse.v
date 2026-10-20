(** Actual arbitrary-index use of a proved Clos carrier. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalContexts NumericalSourceFull
 SourceBounded SourceRecursionClosureSyntax SourceRecursionNextIn SourceConjunctionRules SourceDerivedRules SourceQuantifierRules
 NumericalInstantiation NumericalSubstitutionMaps SubstitutionSource SourceInstantiationConstructors SourceTracePointRules SourceTraceBounds.
Unset Implicit Arguments.
Theorem source_full_rec_closure_next M b c n phi a Y closure x member next:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure M phi a Y closure ->
 sf_relation M SFMember x Y member ->source_rec_next_in M phi x Y next ->
 source_full_prv M b c n closure ->source_full_prv M b c n member ->source_full_prv M b c n next.
Proof.
 intros BP(initial&guard&binary&member0&body&ex&point&all&HInitial&HGuard&HBinary&HMember&HBody&HEx&HPoint&HAll&HClosure)HM HNext PC PM.
 pose proof(source_full_conjunction_right M b c n initial all closure HClosure PC)as PAll.
 assert(HNext0:source_rec_next_in M phi(zeroM M)(succM M Y)ex).
 { exists binary,member0,body. auto. }
 destruct(sf_relation_total M SFImpl member next)as(target&HTarget).
 destruct(substitution_singleton_total M x)as(rb&rc&HHead&_).
 assert(IEx:numerical_instantiation M ex x next).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_next_in_substitution M phi(zeroM M)(succM M Y)ex x Y next rb rc(code_numeral M 1)(zeroM M)BP HNext0 HNext HHead(substitution_singleton_tail M rb rc Y)). }
 pose proof(source_instantiation_binary M SFImpl guard ex point x member next target(or_intror(or_intror eq_refl))HPoint
  (source_instantiation_head_member M Y guard x member HGuard HM)IEx HTarget)as IPoint.
 pose proof(full_source_AllE M b c n point all x target(source_wf_quantifier_instance M b c n SFAll point all x target(or_introl eq_refl)HAll(source_full_prv_wellformed M b c n all PAll)IPoint)PAll HAll IPoint)as PTarget.
 exact(source_full_modus_ponens M b c n member next target HTarget PTarget PM).
Qed.
Print Assumptions source_full_rec_closure_next.
