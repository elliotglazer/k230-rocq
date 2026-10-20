(** Actual numerical source proof of exchanging two universal binders.
    The arbitrary internal matrix is related to the target matrix by an
    actual swap graph, rather than by external substitution notation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalSubstitutionMaps NumericalInstantiation SourceSequents SourceTraceBounds SourceContextTransport
  SourceInstantiationConstructors NumericalSourceFull SourceUniversalDistribution SourceSwap.
Unset Implicit Arguments.

Theorem source_universal_commutation M matrix swapped inner outer inner' outer' out k p q :
  source_bounded M matrix k -> source_bounded M swapped k ->
  source_swap_map M p q -> numerical_renaming M matrix p q (code_numeral M 2) (zeroM M) swapped ->
  sf_relation M SFAll matrix (zeroM M) inner -> sf_relation M SFAll inner (zeroM M) outer ->
  sf_relation M SFAll swapped (zeroM M) inner' -> sf_relation M SFAll inner' (zeroM M) outer' ->
  sf_relation M SFImpl outer outer' out ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) out.
Proof.
  intros HM HMS HSwap HR HI HO HI' HO' HOut.
  pose proof (source_bounded_universal_from_matrix M matrix inner k HM HI) as HBI.
  pose proof (source_bounded_universal_from_matrix M inner outer k HBI HO) as HBO.
  pose proof (source_bounded_universal_from_matrix M swapped inner' k HMS HI') as HBI'.
  pose proof (source_bounded_universal_from_matrix M inner' outer' k HBI' HO') as HBO'.
  assert (HBOut:source_bounded M out k).
  { apply (proj2 (source_bounded_accept_binary M SFImpl outer outer' out k
      ltac:(unfold sf_binary;auto) HOut)). auto. }
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) outer) as (b&c&n&HC).
  assert (HBC:context_bounded M b c n k).
  { apply (proj2 (context_bounded_cons M _ _ _ outer b c n k HC)). split;[exact HBO|apply context_bounded_empty]. }
  destruct (context_shift_total M b c n) as (d&e&HS1).
  pose proof (source_context_finite_bound_shift M b c n d e (ex_intro _ k HBC) HS1) as HBD.
  destruct (context_shift_total M d e n) as (u&v&HS2).
  pose proof (source_context_finite_bound_shift M d e n u v HBD HS2) as HBU.
  assert (HMem:context_member M b c n outer).
  { apply (proj2 (context_member_cons M _ _ _ outer b c n outer HC)). now left. }
  destruct (context_renaming_member_forward M b c n (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) d e outer HS1 HMem) as (shiftedOuter&HMemShift&HRShift).
  apply (proj1 (numerical_renaming_quantifier M true inner outer (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) shiftedOuter HO)) in HRShift.
  destruct HRShift as (rb&rc&rn&shiftedInner&HL1&HRInner&HSOuter).
  apply (proj1 (numerical_renaming_quantifier M true matrix inner rb rc rn
    (succM M (zeroM M)) shiftedInner HI)) in HRInner.
  destruct HRInner as (tb&tc&tn&shiftedMatrix&HL2&HRMatrix&HSInner).
  destruct HBD as (bound&HBound).
  pose proof (HBound shiftedOuter HMemShift) as HBShiftedOuter.
  pose proof (proj1 (source_bounded_accept_unary M SFAll shiftedInner shiftedOuter bound
    (or_introl eq_refl) HSOuter) HBShiftedOuter) as HBShiftedInner.
  pose proof (source_full_shifted_universal_hyp M d e n u v shiftedInner shiftedOuter
    (succM M bound) (ex_intro _ bound HBound) HS2 HMemShift HBShiftedInner HSOuter) as HPInner.
  destruct (substitution_singleton_total M (code_numeral M 1)) as (sb&sc&HHead&_).
  assert (HInst:numerical_instantiation M shiftedMatrix (code_numeral M 1) swapped).
  { exists sb,sc. split;[exact HHead|].
    exact (source_twice_lifted_shift_swap_instance M matrix k rb rc tb tc rn p q tn
      shiftedMatrix swapped sb sc HM HL1 HL2 HRMatrix HSwap HR HHead). }
  assert (HPSwapped:source_full_prv M u v n swapped).
  { apply (full_source_AllE M u v n shiftedMatrix shiftedInner (code_numeral M 1) swapped).
    - exact (source_bounded_in_context_wf M u v n swapped k HMS HBU).
    - exact HPInner.
    - exact HSInner.
    - exact HInst. }
  apply (full_source_II M (zeroM M) (zeroM M) (zeroM M) outer outer' out b c n).
  - exists k. split;[exact HBOut|apply context_bounded_empty].
  - apply (full_source_AllI M b c n inner' outer' d e).
    + exists k. auto.
    + apply (full_source_AllI M d e n swapped inner' u v).
      * exact (source_bounded_in_context_wf M d e n inner' k HBI' (ex_intro _ bound HBound)).
      * exact HPSwapped.
      * exact HS2.
      * exact HI'.
    + exact HS1.
    + exact HO'.
  - exact HC.
  - exact HOut.
Qed.

Print Assumptions source_universal_commutation.
