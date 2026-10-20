(** Preserve the actual definability witness while converting its
    set-level profile to the L-Separation profile. The two upstream
    hierarchy/reflection inputs are ordinary proofs, not a target schema. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceRelativizationBounds NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming SourceQuantifierRules NumericalSourceFull
  SourceSequents SourceProofWeakening SourceExistentialMap SourceContextProofHelpers
  SourcePropositionalTemplates SourceLSeparationPoint SourceLSeparationProfile.
Unset Implicit Arguments.

Theorem source_full_L_separation_witness M domain rho k b c n u v
    definition reflection transitive result alld allr allt allresult guarded guardedall
    defbody defex outbody outex :
  source_bounded M domain (code_numeral M 1) ->
  (forall i,source_bounded M (rho i) (succM M (succM M k))) ->
  context_bounded M b c n k ->source_bounded M defex k ->context_shift M b c n u v ->
  code_relation M rho (source_prop_expression lsep_definition_point) definition ->
  code_relation M rho (source_prop_expression lsep_reflection_point) reflection ->
  code_relation M rho (source_prop_expression lsep_transitive_point) transitive ->
  code_relation M rho (source_prop_expression lsep_result_point) result ->
  sf_relation M SFAll definition (zeroM M) alld ->sf_relation M SFAll reflection (zeroM M) allr ->
  sf_relation M SFAll transitive (zeroM M) allt ->sf_relation M SFAll result (zeroM M) allresult ->
  sf_relation M SFImpl domain result guarded ->sf_relation M SFAll guarded (zeroM M) guardedall ->
  sf_relation M SFAnd domain alld defbody ->sf_relation M SFEx defbody (zeroM M) defex ->
  sf_relation M SFAnd domain guardedall outbody ->sf_relation M SFEx outbody (zeroM M) outex ->
  source_full_prv M b c n defex ->source_full_prv M u v n allr ->source_full_prv M u v n allt ->
  source_full_prv M b c n outex.
Proof.
  intros HD HB HC HDefBound HShift HDef HRef HTrans HResult HAD HAR HAT HAG HI HGAll
    HDB HDE HOB HOE PDef PRef PTrans.
  pose proof (context_shift_preserves_bound M b c n u v k HShift HC) as HUC.
  assert (HGW:source_bounded M guarded (succM M (succM M k))).
  { apply (proj2 (source_bounded_accept_binary M SFImpl domain result guarded
      (succM M (succM M k))(or_intror (or_intror eq_refl)) HI)). split.
    - exact (sr_domain_bound_succ M domain (succM M k) HD).
    - exact (source_prop_template_bound M rho lsep_result_point (succM M (succM M k)) HB result HResult). }
  assert (HGA:source_bounded M guardedall (succM M k)).
  { exact (proj2 (source_bounded_accept_unary M SFAll guarded guardedall (succM M k)
      (or_introl eq_refl) HGAll) HGW). }
  assert (HOutBody:source_bounded M outbody (succM M k)).
  { apply (proj2 (source_bounded_accept_binary M SFAnd domain guardedall outbody
      (succM M k)(or_introl eq_refl) HOB)). split;[exact (sr_domain_bound_succ M domain k HD)|exact HGA]. }
  assert (HOut:source_bounded M outex k).
  { exact (proj2 (source_bounded_accept_unary M SFEx outbody outex k (or_intror eq_refl) HOE) HOutBody). }
  pose proof (proj1 (source_bounded_accept_unary M SFEx defbody defex k (or_intror eq_refl) HDE)
    HDefBound) as HDefBody.
  destruct (environment_cons_total M u v n defbody) as [sb [sc [sn HCons]]].
  assert (HSC:context_bounded M sb sc sn (succM M k)).
  { apply (proj2 (context_bounded_cons M u v n defbody sb sc sn (succM M k) HCons)). auto. }
  pose proof (source_full_cons_head M u v n defbody sb sc sn (succM M k) HCons HDefBody HSC) as PHead.
  assert (PD:source_full_prv M sb sc sn domain).
  { apply (full_source_CE1 M sb sc sn domain alld defbody);[exists (succM M k);split;[exact (sr_domain_bound_succ M domain k HD)|exact HSC]|exact PHead|exact HDB]. }
  assert (PA:source_full_prv M sb sc sn alld).
  { apply (full_source_CE2 M sb sc sn domain alld defbody);[|exact PHead|exact HDB].
    exists (succM M k). split;[|exact HSC].
    exact (proj2 (proj1 (source_bounded_accept_binary M SFAnd domain alld defbody
      (succM M k)(or_introl eq_refl) HDB) HDefBody)). }
  assert (HIn:context_included M u v n sb sc sn).
  { intros h HH. apply (proj2 (context_member_cons M u v n defbody sb sc sn h HCons)). now right. }
  pose proof (source_full_prv_weaken_bounded M u v n sb sc sn allr (succM M k) PRef HIn HSC) as PR.
  pose proof (source_full_prv_weaken_bounded M u v n sb sc sn allt (succM M k) PTrans HIn HSC) as PT.
  pose proof (source_full_L_separation_guarded_profile M domain rho (succM M k) sb sc sn
    definition reflection transitive result alld allr allt allresult guarded guardedall
    HD HB HSC HDef HRef HTrans HResult HAD HAR HAT HAG HI HGAll PA PR PT) as PG.
  assert (POut:source_full_prv M sb sc sn outbody).
  { apply (full_source_CI M sb sc sn domain guardedall outbody);
      [exists (succM M k);auto|exact PD|exact PG|exact HOB]. }
  destruct (numerical_renaming_total M outex (zeroM M)(zeroM M)(zeroM M)(succM M (zeroM M)))
    as [shifted HOutShift].
  exact (source_full_exists_map M b c n defbody outbody defex outex u v sb sc sn shifted
    (ex_intro _ k (conj HOut HC)) HDE HOE HShift HCons HOutShift PDef POut).
Qed.

Print Assumptions source_full_L_separation_witness.
