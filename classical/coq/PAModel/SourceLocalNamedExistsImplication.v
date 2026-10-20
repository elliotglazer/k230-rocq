(** Actual named existential implication in arbitrary bounded contexts.
    Both the context and residual goal have explicit eigenvariable vacuity. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalEnvironments
 NumericalSourceFull SourceNamedQuantifierRules SourceNamedVacuity SourceNamedElimination SourceContextProofHelpers
 SourceUpperProofHelpers.
Unset Implicit Arguments.
Theorem source_full_local_named_exists_implication M gb gc gn name body ex goal point result k:
 context_bounded M gb gc gn k ->source_bounded M body k ->
 source_named_context_vacuous M gb gc gn name ->source_named_vacuous M name goal ->
 source_named_quantifier M false name body ex ->sf_relation M SFImpl body goal point ->
 sf_relation M SFImpl ex goal result ->source_full_prv M gb gc gn point ->source_full_prv M gb gc gn result.
Proof.
 intros BC BB VC VG HE HP HR PPt.
 pose proof(source_named_quantifier_bound M false name body ex k BB HE)as BE.
 destruct(environment_cons_total M gb gc gn ex)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M gb gc gn ex ub uc un k HCons)(conj BE BC))as BU.
 pose proof(source_full_cons_head M gb gc gn ex ub uc un k HCons BE BU)as PEx.
 pose proof(source_full_cons_weaken M gb gc gn ex ub uc un k point HCons BU PPt)as PPoint.
 pose proof(source_named_context_vacuous_cons M gb gc gn ex ub uc un name HCons VC
  (source_named_quantifier_is_vacuous M false name body ex k BB HE))as VU.
 pose proof(source_full_named_exists_elim M ub uc un name body ex goal point VU VG HE HP PPoint PEx)as PGoal.
 exact(source_full_implication_intro M gb gc gn ex goal result ub uc un HCons HR PGoal).
Qed.
Print Assumptions source_full_local_named_exists_implication.
