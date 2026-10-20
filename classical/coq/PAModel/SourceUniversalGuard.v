(** Add a bounded-one domain guard inside an actual universal proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalContexts NumericalContextRenaming SourceBounded NumericalSourceFull
  SourceRelativizationBounds SourceUniversalPropositional SourceGuardedPrefixes.
Unset Implicit Arguments.

Theorem source_full_universal_guard M domain b c n a all guard guardedall :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFAll a (zeroM M) all -> sf_relation M SFImpl domain a guard ->
  sf_relation M SFAll guard (zeroM M) guardedall -> source_full_prv M b c n all ->
  source_full_prv M b c n guardedall.
Proof.
  intros HD HA HG HGuardAll PA.
  destruct (source_full_prv_wellformed M b c n all PA) as [k [HBound HCtx]].
  pose proof (proj1 (source_bounded_accept_unary M SFAll a all k (or_introl eq_refl) HA)
    HBound) as HABound.
  destruct (context_shift_total M b c n) as [u [v HC]].
  apply (full_source_AllI M b c n guard guardedall u v).
  - exists k. split;[|exact HCtx].
    apply (proj2 (source_bounded_accept_unary M SFAll guard guardedall k
      (or_introl eq_refl) HGuardAll)).
    apply (proj2 (source_bounded_accept_binary M SFImpl domain a guard (succM M k)
      (or_intror (or_intror eq_refl)) HG)). split;[|exact HABound].
    exact (sr_domain_bound_succ M domain k HD).
  - apply (source_full_domain_implication M domain u v n a guard HD);[|exact HG].
    exact (source_full_all_shift M b c n a all u v HA PA HC).
  - exact HC.
  - exact HGuardAll.
Qed.

Print Assumptions source_full_universal_guard.
