(** Encoded existential elimination into the native source existential.
    The outer falsity slot is a genuinely refutable formula; the inner
    slot remains explicit and may differ after closing the raw binder. *)
From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SetCodeDescent
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalInstantiation SourceSequents SourceTraceBounds SourceContextTransport
  SourceInstantiationConstructors SourceQuantifierRules NumericalSourceFull SourceProofWeakening
  SourceZFCProvability SourceExistentialShift.
Unset Implicit Arguments.

Theorem source_zfc_encoded_exists_forward M matrix native innerbad innerneg allneg bad
    encoded notbad out :
  sf_relation M SFEx matrix (zeroM M) native ->
  sf_relation M SFImpl matrix innerbad innerneg ->
  sf_relation M SFAll innerneg (zeroM M) allneg ->
  sf_relation M SFImpl allneg bad encoded ->
  sf_relation M SFImpl bad (zeroM M) notbad -> source_zfc_provable M notbad ->
  sf_relation M SFImpl encoded native out ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) native ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) out ->
  source_zfc_provable M out.
Proof.
  intros HEx HInner HAll HE HNot (nb&nc&nn&HNC&HN) HOut HWEx HWO.
  pose proof (source_zfc_context_closed M nb nc nn HNC) as HNB.
  pose proof (source_wf_binary_left M _ _ _ SFImpl encoded native out
    ltac:(unfold sf_binary;auto) HOut HWO) as HWE.
  pose proof (source_wf_binary_left M _ _ _ SFImpl allneg bad encoded
    ltac:(unfold sf_binary;auto) HE HWE) as HWA.
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
  destruct (sf_relation_total M SFImpl native (zeroM M)) as (nex&HNEx).
  pose proof (source_wf_binary M _ _ _ SFImpl native (zeroM M) nex
    ltac:(unfold sf_binary;auto) HNEx HWEx HWF) as HWNEx.
  destruct (environment_cons_total M nb nc nn encoded) as (eb&ec&en&HCE).
  assert (HBE:source_context_finite_bound M eb ec en).
  { apply (source_context_finite_bound_cons M nb nc nn encoded eb ec en
      (ex_intro _ (zeroM M) HNB));[|exact HCE].
    destruct HWE as [k [HK _]]. now exists k. }
  destruct (environment_cons_total M eb ec en nex) as (db&dc&dn&HCN).
  assert (HBD:source_context_finite_bound M db dc dn).
  { apply (source_context_finite_bound_cons M eb ec en nex db dc dn HBE);[|exact HCN].
    destruct HWNEx as [k [HK _]]. now exists k. }
  assert (HPExUnder:source_full_prv M db dc dn native).
  { destruct (context_shift_total M db dc dn) as (sb&sc&HS).
    pose proof (source_context_finite_bound_shift M db dc dn sb sc HBD HS) as HBS.
    assert (HMemN:context_member M db dc dn nex).
    { apply (proj2 (context_member_cons M eb ec en nex db dc dn nex HCN)). now left. }
    destruct (context_renaming_member_forward M db dc dn (zeroM M) (zeroM M)
      (zeroM M) (succM M (zeroM M)) sb sc nex HS HMemN) as (snex&HMemSN&HRN).
    apply (proj1 (numerical_renaming_binary M SFImpl native (zeroM M) nex
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) snex
      ltac:(unfold sf_binary;auto) HNEx)) in HRN.
    destruct HRN as (sex&sz&HREx&HRZ&HSN).
    assert (ESZ:sz = zeroM M).
    { exact (proj1 (numerical_renaming_invalid M (zeroM M) _ _ _ _ sz (or_introl eq_refl)) HRZ). }
    subst sz.
    destruct HWM as [km [HBM HMEmpty]].
    destruct (source_shifted_ex_specialization M matrix native sex km HBM HEx HREx)
      as (shiftmatrix&HShiftEx&HInst).
    assert (HWSEx:source_sequent_wf M sb sc dn sex).
    { apply (source_wf_binary_left M sb sc dn SFImpl sex (zeroM M) snex
        ltac:(unfold sf_binary;auto) HSN).
      destruct HBS as [k HK]. exists k. split;[exact (HK snex HMemSN)|exact HK]. }
    assert (HPAll:source_full_prv M db dc dn allneg).
    { apply (full_source_AllI M db dc dn innerneg allneg sb sc).
      - apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) allneg db dc dn);[|exact HBD].
        exists ka. split;[exact HBA|apply context_bounded_empty].
      - destruct (environment_cons_total M sb sc dn matrix) as (ub&uc&un&HCM).
        assert (HBU:source_context_finite_bound M ub uc un).
        { apply (source_context_finite_bound_cons M sb sc dn matrix ub uc un HBS);[now exists km|exact HCM]. }
        apply (full_source_II M sb sc dn matrix innerbad innerneg ub uc un).
        + exact (source_wf_transport_context M _ _ _ innerneg sb sc dn HWI HBS).
        + apply full_source_Exp.
          * exact (source_wf_transport_context M _ _ _ innerbad ub uc un HWIB HBU).
          * apply (full_source_IE M ub uc un sex (zeroM M) snex).
            -- exact (source_wf_transport_context M _ _ _ (zeroM M) ub uc un HWF HBU).
            -- apply full_source_Ctx.
               ++ apply (source_wf_binary M ub uc un SFImpl sex (zeroM M) snex
                    ltac:(unfold sf_binary;auto) HSN).
                  ** exact (source_wf_transport_context M _ _ _ sex ub uc un HWSEx HBU).
                  ** exact (source_wf_transport_context M _ _ _ (zeroM M) ub uc un HWF HBU).
               ++ apply (proj2 (context_member_cons M sb sc dn matrix ub uc un snex HCM)). now right.
            -- apply (full_source_ExI M ub uc un shiftmatrix sex (zeroM M) matrix).
               ++ exact (source_wf_transport_context M _ _ _ sex ub uc un HWSEx HBU).
               ++ apply full_source_Ctx.
                  ** apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) matrix ub uc un);[|exact HBU].
                     now exists km.
                  ** apply (proj2 (context_member_cons M sb sc dn matrix ub uc un matrix HCM)). now left.
               ++ exact HShiftEx.
               ++ exact HInst.
            -- exact HSN.
        + exact HCM.
        + exact HInner.
      - exact HS.
      - exact HAll. }
    assert (HPEncoded:source_full_prv M db dc dn encoded).
    { apply full_source_Ctx.
      - exact (source_wf_transport_context M _ _ _ encoded db dc dn HWE HBD).
      - apply (proj2 (context_member_cons M eb ec en nex db dc dn encoded HCN)). right.
        apply (proj2 (context_member_cons M nb nc nn encoded eb ec en encoded HCE)). now left. }
    assert (HPBad:source_full_prv M db dc dn bad).
    { apply (full_source_IE M db dc dn allneg bad encoded);[|exact HPEncoded|exact HPAll|exact HE].
      apply (source_wf_binary_right M db dc dn SFImpl allneg bad encoded
        ltac:(unfold sf_binary;auto) HE).
      exact (source_full_prv_wellformed M db dc dn encoded HPEncoded). }
    destruct HBD as [bound HBound].
    assert (HN':source_full_prv M db dc dn notbad).
    { apply (source_full_prv_weaken_bounded M nb nc nn db dc dn notbad bound HN);[|exact HBound].
      intros f HF. apply (proj2 (context_member_cons M eb ec en nex db dc dn f HCN)). right.
      apply (proj2 (context_member_cons M nb nc nn encoded eb ec en f HCE)). now right. }
    apply full_source_Exp.
    - exact (source_wf_transport_context M _ _ _ native db dc dn HWEx (ex_intro _ bound HBound)).
    - apply (full_source_IE M db dc dn bad (zeroM M) notbad);[|exact HN'|exact HPBad|exact HNot].
      exact (source_wf_transport_context M _ _ _ (zeroM M) db dc dn HWF (ex_intro _ bound HBound)). }
  destruct (sf_relation_total M SFImpl nex native) as (y&HY).
  destruct (sf_relation_total M SFImpl y native) as (pc&HPC).
  pose proof (source_wf_transport_context M _ _ _ native eb ec en HWEx HBE) as HWExE.
  pose proof (source_wf_transport_context M _ _ _ nex eb ec en HWNEx HBE) as HWNExE.
  pose proof (source_wf_binary M eb ec en SFImpl nex native y
    ltac:(unfold sf_binary;auto) HY HWNExE HWExE) as HWY.
  pose proof (full_source_II M eb ec en nex native y db dc dn HWY HPExUnder HCN HY) as HPY.
  assert (HPExE:source_full_prv M eb ec en native).
  { apply (full_source_IE M eb ec en y native pc HWExE);[|exact HPY|exact HPC].
    apply (full_source_Pc M eb ec en native (zeroM M) nex y pc);[|exact HNEx|exact HY|exact HPC].
    exact (source_wf_binary M eb ec en SFImpl y native pc
      ltac:(unfold sf_binary;auto) HPC HWY HWExE). }
  exists nb,nc,nn. split;[exact HNC|].
  apply (full_source_II M nb nc nn encoded native out eb ec en).
  - exact (source_wf_transport_context M _ _ _ out nb nc nn HWO (ex_intro _ (zeroM M) HNB)).
  - exact HPExE.
  - exact HCE.
  - exact HOut.
Qed.

Print Assumptions source_zfc_encoded_exists_forward.
