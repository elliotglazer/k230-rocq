(** Source relativization preserves existential elimination with separate
    domain and body assumptions, in the order used by relative contexts. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming SourceSequents
  SourceQuantifierRules NumericalSourceFull SourceRelativization
  SourceRelativizationBounds SourceRelativizedExistsElimination SourceGuardedBranch.
Unset Implicit Arguments.

Theorem source_relativized_ExE_two_wf M domain a ex f g ra rex rf rg
    b c n u v db dc dn ab ac an :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx a (zeroM M) ex -> source_formula_shift M f g ->
  source_relativization M domain a ra -> source_relativization M domain ex rex ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  context_shift M b c n u v ->
  environment_cons M u v n domain db dc dn ->
  environment_cons M db dc dn ra ab ac an ->
  source_sequent_wf M b c n rf ->
  source_full_prv M b c n rex -> source_full_prv M ab ac an rg ->
  source_full_prv M b c n rf.
Proof.
  intros HD HEx HS HRA HREx HRF HRG HShift HDom HBody HWF PEx PBranch.
  destruct (sf_relation_total M SFAnd domain ra) as [guard HGuard].
  destruct (environment_cons_total M u v n guard) as [gb [gc [gn HCons]]].
  apply (source_relativized_ExE_guarded_wf M domain a ex f g ra rex rf rg guard
    b c n u v gb gc gn HD HEx HS HRA HREx HRF HRG HGuard HShift HCons HWF PEx).
  exact (source_guarded_branch_from_two M u v n domain ra rg guard
    db dc dn ab ac an gb gc gn HDom HBody HCons HGuard PBranch).
Qed.

Theorem source_relativized_ExE_two M domain a ex f g ra rex rf rg
    b c n u v db dc dn ab ac an k :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M f k -> context_bounded M b c n k ->
  sf_relation M SFEx a (zeroM M) ex -> source_formula_shift M f g ->
  source_relativization M domain a ra -> source_relativization M domain ex rex ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  context_shift M b c n u v ->
  environment_cons M u v n domain db dc dn ->
  environment_cons M db dc dn ra ab ac an ->
  source_full_prv M b c n rex -> source_full_prv M ab ac an rg ->
  source_full_prv M b c n rf.
Proof.
  intros HD HB HC HEx HS HRA HREx HRF HRG HShift HDom HBody PEx PBranch.
  apply (source_relativized_ExE_two_wf M domain a ex f g ra rex rf rg
    b c n u v db dc dn ab ac an HD HEx HS HRA HREx HRF HRG HShift HDom HBody);try assumption.
  exists k. split;[|exact HC].
  exact (source_relativization_preserves_bound M f domain k rf HD HB HRF).
Qed.

Print Assumptions source_relativized_ExE_two_wf.
Print Assumptions source_relativized_ExE_two.
