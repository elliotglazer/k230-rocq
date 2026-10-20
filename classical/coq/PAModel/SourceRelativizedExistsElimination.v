(** Exact existential elimination from the guarded branch. The branch
    assumption is D(0) /\ body. Separating that assumption into two entries
    of an arbitrary proof context is a distinct structural rule. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming SourceSequents
  SourceQuantifierRules NumericalSourceFull SourceRelativizationRules SourceRelativization
  SourceRelativizationFunctionality SourceRelativizationBounds SourceRelativizationInstances.
Unset Implicit Arguments.

Theorem source_relativized_formula_shift M domain f g rf rg :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f rf -> source_formula_shift M f g ->
  source_relativization M domain g rg -> source_formula_shift M rf rg.
Proof.
  intros HD HRF HS HRG.
  destruct (source_relativization_shift_exists M domain f rf g HD HRF HS)
    as [shifted [HRShift HSShift]].
  pose proof (source_relativization_functional M g domain shifted rg HRShift HRG) as E.
  now subst shifted.
Qed.

Theorem source_relativized_ExE_guarded_wf M domain a ex f g ra rex rf rg guard
    b c n u v x y l :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx a (zeroM M) ex -> source_formula_shift M f g ->
  source_relativization M domain a ra -> source_relativization M domain ex rex ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  sf_relation M SFAnd domain ra guard ->
  context_shift M b c n u v -> environment_cons M u v n guard x y l ->
  source_sequent_wf M b c n rf ->
  source_full_prv M b c n rex -> source_full_prv M x y l rg ->
  source_full_prv M b c n rf.
Proof.
  intros HD HEx HS HRA HREx HRF HRG HGuard HC HCons HWF PEx PBranch.
  destruct (source_relativization_quantifier_inv M domain false a ex rex HEx HREx)
    as [body [HBody [mid [HMid HQuant]]]].
  pose proof (source_relativization_functional M a domain body ra HBody HRA) as E.
  subst body.
  pose proof (sf_relation_functional M SFAnd domain ra mid guard HMid HGuard) as E.
  subst mid.
  apply (full_source_ExE M b c n guard rex rf rg u v x y l HWF PEx PBranch
    HQuant HC HCons).
  exact (source_relativized_formula_shift M domain f g rf rg HD HRF HS HRG).
Qed.

Theorem source_relativized_ExE_guarded M domain a ex f g ra rex rf rg guard
    b c n u v x y l k :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M f k -> context_bounded M b c n k ->
  sf_relation M SFEx a (zeroM M) ex -> source_formula_shift M f g ->
  source_relativization M domain a ra -> source_relativization M domain ex rex ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  sf_relation M SFAnd domain ra guard ->
  context_shift M b c n u v -> environment_cons M u v n guard x y l ->
  source_full_prv M b c n rex -> source_full_prv M x y l rg ->
  source_full_prv M b c n rf.
Proof.
  intros HD HB HBound HEx HS HRA HREx HRF HRG HGuard HC HCons PEx PBranch.
  apply (source_relativized_ExE_guarded_wf M domain a ex f g ra rex rf rg guard
    b c n u v x y l HD HEx HS HRA HREx HRF HRG HGuard HC HCons);try assumption.
  exists k. split;[|exact HBound].
  exact (source_relativization_preserves_bound M f domain k rf HD HB HRF).
Qed.

Print Assumptions source_relativized_formula_shift.
Print Assumptions source_relativized_ExE_guarded_wf.
Print Assumptions source_relativized_ExE_guarded.
