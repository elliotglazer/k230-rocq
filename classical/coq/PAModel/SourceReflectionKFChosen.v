(** The actual chosen K-closure witness, from a closure step and ordinal chart. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalInstantiation NumericalContexts NumericalSourceFull SourceConjunctionRules SourceNamedProofRules
 SourceOrdinalPredicate SourceHierarchySyntax SourcePieceConjunction
 SourceReflectionOrdinalChart SourceReflectionOrdinalChartRules SourceReflectionStep
 SourceReflectionStepProperties SourceReflectionKFWitness.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_full_reflection_KF_chosen M b c n domain level sb sc count Y K x w chart step ordinal memberY target:
 source_reflection_ordinal_chart M Y K chart ->source_reflection_step M domain level sb sc count x w step ->
 numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->sf_relation M SFMember w Y memberY ->
 source_reflection_KF_witness M domain level sb sc count K x w target ->
 source_full_prv M b c n chart ->source_full_prv M b c n step ->source_full_prv M b c n ordinal ->source_full_prv M b c n memberY ->
 source_full_prv M b c n target.
Proof.
 intros HC HS HO HMY(m&t&l&p&q&all&i&HM&HT&HL&HP&HQ&HA&HI&HF)PC PS PO PMY.
 destruct(source_full_reflection_step_properties M b c n domain level sb sc count x w step ordinal HS HO PS PO)
  as(ow&t'&l'&p'&q'&all'&HOW&HT'&HL'&HP'&HQ'&HA'&POW&PT&PAll).
 assert(E:t'=t)by(eapply sf_relation_functional;eassumption). subst t'.
 assert(E:l'=l)by(eapply source_LL_instance_functional;eassumption). subst l'.
 assert(E:p'=p)by(eapply source_piece_conjunction_functional;eassumption). subst p'.
 assert(E:q'=q)by(eapply sf_relation_functional;eassumption). subst q'.
 assert(E:all'=all)by(eapply sf_relation_functional;eassumption). subst all'.
 pose proof(source_full_reflection_ordinal_chart_in M b c n Y K chart w m memberY ow HC HM HMY HOW PC PMY POW)as PM.
 exact(source_full_and_intro M b c n m i target HF PM(source_full_and_intro M b c n t all i HI PT PAll)).
Qed.
Print Assumptions source_full_reflection_KF_chosen.
