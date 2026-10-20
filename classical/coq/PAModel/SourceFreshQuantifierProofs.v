(** Actual raw-binder proof rules at a fresh named witness. Original source
    parameters and the ambient context remain fixed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalInstantiation NumericalSourceFull SourceNamedVacuity SourceNamedElimination
 SourceNamedQuantifierRules SourceFreshNamedOpening.
Unset Implicit Arguments.

Theorem source_full_fresh_exists_elim M b c n body ex x opened goal imp k:
 context_bounded M b c n k ->source_bounded M body(succM M k) ->source_bounded M goal k ->
 coding_lt M k(succM M x) ->sf_relation M SFEx body(zeroM M)ex ->
 numerical_instantiation M body x opened ->sf_relation M SFImpl opened goal imp ->
 source_full_prv M b c n imp ->source_full_prv M b c n ex ->source_full_prv M b c n goal.
Proof.
 intros HC HB HG HX HEx HI HImp PImp PEx.
 assert(HV:source_named_context_vacuous M b c n x).
 { intros f HF. exact(source_named_vacuous_above_bound M f x k(HC f HF)HX). }
 exact(source_full_named_exists_elim M b c n x opened ex goal imp HV
  (source_named_vacuous_above_bound M goal x k HG HX)
  (source_fresh_instantiation_named_quantifier M false body ex x opened k HB HX HI HEx)HImp PImp PEx).
Qed.

Theorem source_full_fresh_all_intro M b c n body all x opened k:
 context_bounded M b c n k ->source_bounded M body(succM M k) ->coding_lt M k(succM M x) ->
 sf_relation M SFAll body(zeroM M)all ->numerical_instantiation M body x opened ->
 source_full_prv M b c n opened ->source_full_prv M b c n all.
Proof.
 intros HC HB HX HAll HI POpened.
 assert(HV:source_named_context_vacuous M b c n x).
 { intros f HF. exact(source_named_vacuous_above_bound M f x k(HC f HF)HX). }
 exact(source_full_named_quantifier_all_intro M b c n x opened all HV
  (source_fresh_instantiation_named_quantifier M true body all x opened k HB HX HI HAll)POpened).
Qed.
Print Assumptions source_full_fresh_exists_elim.
Print Assumptions source_full_fresh_all_intro.
