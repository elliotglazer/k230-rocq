(** Native existential elimination proves the converse encoded form. The
    closed binder's falsity slot is refuted in the actual source theory;
    it is not identified with the source falsity constructor. *)
From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SetCodeDescent
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalInstantiation SourceSequents SourceTraceBounds SourceContextTransport
  SourceInstantiationConstructors SourceQuantifierRules NumericalSourceFull SourceProofWeakening
  SourceZFCProvability SourceClosedContextShift SourceUniversalPropositional.
Unset Implicit Arguments.

Theorem source_zfc_encoded_exists_reverse M matrix native innerbad innerneg allneg bad
    encoded notinnerbad out :
  sf_relation M SFEx matrix (zeroM M) native ->
  sf_relation M SFImpl matrix innerbad innerneg ->
  sf_relation M SFAll innerneg (zeroM M) allneg ->
  sf_relation M SFImpl allneg bad encoded ->
  sf_relation M SFImpl innerbad (zeroM M) notinnerbad -> source_zfc_provable M notinnerbad ->
  sf_relation M SFImpl native encoded out ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) native ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) out ->
  source_zfc_provable M out.
Proof.
  intros HEx HInner HAll HE HNot (nb&nc&nn&HNC&HN) HOut HWEx HWO.
  pose proof (source_zfc_context_closed M nb nc nn HNC) as HNB.
  pose proof (source_wf_binary_right M _ _ _ SFImpl native encoded out
    ltac:(unfold sf_binary;auto) HOut HWO) as HWE.
  pose proof (source_wf_binary_left M _ _ _ SFImpl allneg bad encoded
    ltac:(unfold sf_binary;auto) HE HWE) as HWA.
  pose proof (source_wf_binary_right M _ _ _ SFImpl allneg bad encoded
    ltac:(unfold sf_binary;auto) HE HWE) as HWBad.
  destruct HWA as [ka [HBA _]].
  pose proof (proj1 (source_bounded_accept_unary M SFAll innerneg allneg ka
    (or_introl eq_refl) HAll) HBA) as HBI.
  assert (HWI:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) innerneg).
  { exists (succM M ka). split;[exact HBI|apply context_bounded_empty]. }
  pose proof (source_wf_binary_left M _ _ _ SFImpl matrix innerbad innerneg
    ltac:(unfold sf_binary;auto) HInner HWI) as HWM.
  pose proof (source_wf_binary_right M _ _ _ SFImpl matrix innerbad innerneg
    ltac:(unfold sf_binary;auto) HInner HWI) as HWIB.
  assert (HWF:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) (zeroM M)).
  { exists (zeroM M). split;[apply source_bounded_accept_falsity|apply context_bounded_empty]. }
  destruct (environment_cons_total M nb nc nn native) as (eb&ec&en&HCE).
  assert (HBE:source_context_finite_bound M eb ec en).
  { apply (source_context_finite_bound_cons M nb nc nn native eb ec en
      (ex_intro _ (zeroM M) HNB));[|exact HCE].
    destruct HWEx as [k [HK _]]. now exists k. }
  destruct (environment_cons_total M eb ec en allneg) as (db&dc&dn&HCA).
  assert (HBD:source_context_finite_bound M db dc dn).
  { apply (source_context_finite_bound_cons M eb ec en allneg db dc dn HBE);[now exists ka|exact HCA]. }
  assert (HPBad:source_full_prv M db dc dn bad).
  { destruct (context_shift_total M db dc dn) as (sb&sc&HS).
    pose proof (source_context_finite_bound_shift M db dc dn sb sc HBD HS) as HBS.
    destruct (environment_cons_total M sb sc dn matrix) as (ub&uc&un&HCM).
    assert (HBU:source_context_finite_bound M ub uc un).
    { apply (source_context_finite_bound_cons M sb sc dn matrix ub uc un HBS);[|exact HCM].
      destruct HWM as [k [HK _]]. now exists k. }
    assert (HPAll:source_full_prv M db dc dn allneg).
    { apply full_source_Ctx.
      - apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) allneg db dc dn);[|exact HBD].
        exists ka. split;[exact HBA|apply context_bounded_empty].
      - apply (proj2 (context_member_cons M eb ec en allneg db dc dn allneg HCA)). now left. }
    pose proof (source_full_all_shift M db dc dn innerneg allneg sb sc HAll HPAll HS) as HPI.
    assert (HPI':source_full_prv M ub uc un innerneg).
    { destruct HBU as [bound HB].
      apply (source_full_prv_weaken_bounded M sb sc dn ub uc un innerneg bound HPI);[|exact HB].
      intros f HF. apply (proj2 (context_member_cons M sb sc dn matrix ub uc un f HCM)). now right. }
    assert (HPInnerBad:source_full_prv M ub uc un innerbad).
    { apply (full_source_IE M ub uc un matrix innerbad innerneg).
      - exact (source_wf_transport_context M _ _ _ innerbad ub uc un HWIB HBU).
      - exact HPI'.
      - apply full_source_Ctx.
        + exact (source_wf_transport_context M _ _ _ matrix ub uc un HWM HBU).
        + apply (proj2 (context_member_cons M sb sc dn matrix ub uc un matrix HCM)). now left.
      - exact HInner. }
    assert (HN':source_full_prv M ub uc un notinnerbad).
    { destruct HBU as [bound HB].
      apply (source_full_prv_weaken_bounded M nb nc nn ub uc un notinnerbad bound HN);[|exact HB].
      intros f HF. apply (proj2 (context_member_cons M sb sc dn matrix ub uc un f HCM)). right.
      apply (source_context_included_shift M nb nc nn db dc dn nb nc sb sc).
      - intros g HG. apply (proj2 (context_member_cons M eb ec en allneg db dc dn g HCA)). right.
        apply (proj2 (context_member_cons M nb nc nn native eb ec en g HCE)). now right.
      - exact (source_closed_context_shift_self M nb nc nn HNB).
      - exact HS.
      - exact HF. }
    assert (HPFalseBranch:source_full_prv M ub uc un (zeroM M)).
    { apply (full_source_IE M ub uc un innerbad (zeroM M) notinnerbad).
      - exact (source_wf_transport_context M _ _ _ (zeroM M) ub uc un HWF HBU).
      - exact HN'.
      - exact HPInnerBad.
      - exact HNot. }
    apply full_source_Exp.
    - exact (source_wf_transport_context M _ _ _ bad db dc dn HWBad HBD).
    - apply (full_source_ExE M db dc dn matrix native (zeroM M) (zeroM M) sb sc ub uc un).
      + exact (source_wf_transport_context M _ _ _ (zeroM M) db dc dn HWF HBD).
      + apply full_source_Ctx.
        * exact (source_wf_transport_context M _ _ _ native db dc dn HWEx HBD).
        * apply (proj2 (context_member_cons M eb ec en allneg db dc dn native HCA)). right.
          apply (proj2 (context_member_cons M nb nc nn native eb ec en native HCE)). now left.
      + exact HPFalseBranch.
      + exact HEx.
      + exact HS.
      + exact HCM.
      + apply (proj2 (numerical_renaming_invalid M (zeroM M) _ _ _ _ (zeroM M) (or_introl eq_refl))).
        reflexivity. }
  exists nb,nc,nn. split;[exact HNC|].
  apply (full_source_II M nb nc nn native encoded out eb ec en).
  - exact (source_wf_transport_context M _ _ _ out nb nc nn HWO (ex_intro _ (zeroM M) HNB)).
  - apply (full_source_II M eb ec en allneg bad encoded db dc dn).
    + exact (source_wf_transport_context M _ _ _ encoded eb ec en HWE HBE).
    + exact HPBad.
    + exact HCA.
    + exact HE.
  - exact HCE.
  - exact HOut.
Qed.

Print Assumptions source_zfc_encoded_exists_reverse.
