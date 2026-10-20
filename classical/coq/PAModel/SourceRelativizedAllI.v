(** A guarded universal is introduced by discharging the explicit D(0)
    source assumption, followed by the ordinary source AllI rule. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming SourceSequents
  NumericalSourceFull SourceRelativizationRules SourceRelativization
  SourceRelativizationFunctionality SourceRelativizationBounds.
Unset Implicit Arguments.

Theorem source_relativized_AllI_wf M domain a f ra rf b c n u v x y l :
  sf_relation M SFAll a (zeroM M) f ->
  source_relativization M domain a ra -> source_relativization M domain f rf ->
  context_shift M b c n u v -> environment_cons M u v n domain x y l ->
  source_sequent_wf M b c n rf -> source_full_prv M x y l ra ->
  source_full_prv M b c n rf.
Proof.
  intros HF HRA HRF HShift HCons HWF PBody.
  destruct (source_relativization_quantifier_inv M domain true a f rf HF HRF)
    as [body [HBody [mid [HMid HAll]]]].
  pose proof (source_relativization_functional M a domain body ra HBody HRA) as E.
  subst body.
  assert (HWFMid:source_sequent_wf M u v n mid).
  { destruct HWF as [k [HB HC]]. exists (succM M k). split.
    - exact (proj1 (source_bounded_accept_unary M SFAll mid rf k (or_introl eq_refl) HAll) HB).
    - exact (context_shift_preserves_bound M b c n u v k HShift HC). }
  apply (full_source_AllI M b c n mid rf u v HWF).
  - exact (full_source_II M u v n domain ra mid x y l HWFMid PBody HCons HMid).
  - exact HShift.
  - exact HAll.
Qed.

Theorem source_relativized_AllI M domain a f ra rf b c n u v x y l k :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M f k -> context_bounded M b c n k ->
  sf_relation M SFAll a (zeroM M) f ->
  source_relativization M domain a ra -> source_relativization M domain f rf ->
  context_shift M b c n u v -> environment_cons M u v n domain x y l ->
  source_full_prv M x y l ra -> source_full_prv M b c n rf.
Proof.
  intros HD HB HC HF HRA HRF HShift HCons PBody.
  apply (source_relativized_AllI_wf M domain a f ra rf b c n u v x y l
    HF HRA HRF HShift HCons);[|exact PBody].
  exists k. split;[|exact HC].
  exact (source_relativization_preserves_bound M f domain k rf HD HB HRF).
Qed.

Print Assumptions source_relativized_AllI_wf.
Print Assumptions source_relativized_AllI.
