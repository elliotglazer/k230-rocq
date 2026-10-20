(** Actual inner branch of D0 monotonicity: the smaller hierarchy level
    captures a witness, and hierarchy inclusion places it in the larger. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
  SourceHierarchySubsetShell SourceHierarchySubsetUse SourceHierarchySyntax SourceD0At SourceD0Specialization
  SourceEwMonotone SourceRelativizationBounds.
Unset Implicit Arguments.

Theorem source_full_d0_monotone_point M b c n k domain phi d e u v d0 od oe subset ld le result law ewU ewV :
  context_bounded M b c n k ->source_bounded M domain (code_numeral M 1) ->
  source_bounded M phi (succM M k) ->coding_lt M u k ->coding_lt M v k ->
  source_d0_at M domain phi d d0 ->
  source_hierarchy_subset_shell M d e u v od oe subset ld le result law ->
  source_ew_at M domain phi u ewU ->source_ew_at M domain phi v ewV ->
  source_full_prv M b c n law ->source_full_prv M b c n od ->source_full_prv M b c n oe ->
  source_full_prv M b c n subset ->source_full_prv M b c n ld ->source_full_prv M b c n le ->
  source_full_prv M b c n d0 ->source_full_prv M b c n ewV.
Proof.
  intros HC HD HB HU HV HD0 HShell HEU HEV PLaw PD PE PS PLD PLE P0.
  destruct HShell as (HOD&HOE&HSub&HLD&HLE&HResult&HLaw).
  assert (PResult:source_full_prv M b c n result).
  { apply (source_full_hierarchy_subset_use M b c n d e u v od oe subset ld le result law);
      [repeat split;assumption|exact PLaw|exact PD|exact PE|exact PS|exact PLD|exact PLE]. }
  pose proof (source_full_d0_at_specialization M b c n domain phi d d0 u ld ewU (succM M k)
    HD HB HD0 HLD HEU P0 PLD) as PW.
  exact (source_full_ew_monotone M b c n k domain phi u v result ewU ewV HC
    (sr_domain_bound_succ M domain k HD) HB HU HV HResult HEU HEV PResult PW).
Qed.

Print Assumptions source_full_d0_monotone_point.
