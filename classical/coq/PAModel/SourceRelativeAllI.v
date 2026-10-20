(** AllI in the combined mapped/domain context.  Its premise is uniform in
    the numerical representation, as required by the source-row invariant. *)
From PAModel Require Import Model CodeExpressions NumericalContexts
  NumericalEnvironments NumericalContextRenaming NumericalSourceFull SetFormulaCodes
  SourceBounded SourceRelativization SourceRelativeContexts SourceRelativizedAllI.
Unset Implicit Arguments.

Theorem source_relative_AllI_uniform M domain b c n k a f ra rf u v l bs cs :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M f k -> context_bounded M b c n k ->
  sf_relation M SFAll a (zeroM M) f ->
  source_relativization M domain a ra -> source_relativization M domain f rf ->
  source_relative_context M domain b c n k u v l ->
  context_shift M b c n bs cs ->
  (forall tb tc tn,source_relative_context M domain bs cs n (succM M k) tb tc tn ->
    source_full_prv M tb tc tn ra) ->
  source_full_prv M u v l rf.
Proof.
  intros HD HF HC HAll HRA HRF HRel HShift PBody.
  destruct (context_shift_total M u v l) as [su [sv HS]].
  destruct (environment_cons_total M su sv l domain) as [du [dv [dn HCons]]].
  pose proof (source_relative_context_shift_cons M domain b c n k u v l
    bs cs su sv du dv dn HD HRel HShift HS HCons) as HBodyContext.
  exact (source_relativized_AllI M domain a f ra rf u v l su sv du dv dn k
    HD HF (source_relative_context_bounded M domain b c n k u v l HD HC HRel)
    HAll HRA HRF HS HCons (PBody du dv dn HBodyContext)).
Qed.

Print Assumptions source_relative_AllI_uniform.
