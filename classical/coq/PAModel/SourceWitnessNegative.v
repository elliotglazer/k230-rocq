(** The complete no-witness branch of the D0 request.  The universal
    level guard is arbitrary, while both existential matrices are tied
    to the actual source cutoff and guarded-quantifier graphs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceSequents
  SourceD0Recipe SourceFiniteCutoffShift SourceRelativizationRules SourceRelativizationFunctionality
  NumericalRenaming SourceGuardedWitnessShift SourceWitnessVacuity NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_no_witness_request M b c n domain phi shifted test neg level ew point all :
  source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M 1 phi shifted ->
  sr_quantifier M false domain phi test ->sf_relation M SFImpl test(zeroM M) neg ->
  source_ew_recipe M domain shifted ew ->sf_relation M SFImpl level ew point ->
  sf_relation M SFAll point(zeroM M) all ->source_sequent_wf M b c n all ->
  source_full_prv M b c n neg ->source_full_prv M b c n all.
Proof.
  intros HD HC HT HN (atom&left&right&HA&HL&HR&HEw) HP HQ HW PN.
  destruct(numerical_renaming_total M test(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(shiftedTest&HShift).
  pose proof(source_guarded_witness_shift M domain phi shifted test shiftedTest HD HC HT HShift) as HG.
  pose proof(sr_quantifier_functional M false domain shifted shiftedTest left HG HL) as E.
  subst shiftedTest.
  exact(source_full_vacuous_witness_all M b c n test left neg level right ew point all
    HShift HN HEw HP HQ HW PN).
Qed.

Print Assumptions source_full_no_witness_request.
