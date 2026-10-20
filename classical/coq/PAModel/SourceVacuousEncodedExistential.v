(** An encoded existential with a vacuous source matrix implies any chosen
    instance of that matrix.  Both encoded falsity and classical reasoning
    are handled by actual source proof rules. *)
From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SetCodeDescent
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalInstantiation SourceSequents SourceTraceBounds SourceContextTransport
  SourceInstantiationConstructors SourceQuantifierRules NumericalSourceFull SourceProofWeakening
  SourceZFCProvability.
Unset Implicit Arguments.

Theorem source_zfc_vacuous_encoded_exists M body closed quantified shifted bad closebad
    notbad outer_matrix outer_all encoded witness out :
  sf_relation M SFAll closed (zeroM M) quantified ->
  numerical_instantiation M closed witness body ->
  source_formula_shift M quantified shifted ->
  sf_relation M SFImpl shifted closebad outer_matrix ->
  sf_relation M SFAll outer_matrix (zeroM M) outer_all ->
  sf_relation M SFImpl outer_all bad encoded ->
  sf_relation M SFImpl bad (zeroM M) notbad -> source_zfc_provable M notbad ->
  sf_relation M SFImpl encoded body out ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) quantified ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) out ->
  source_zfc_provable M out.
Proof.
  intros HQ HInst HShift HMatrix HAll HE HNot (nb&nc&nn&HNC&HN) HOut HWQ HWO.
  pose proof (source_zfc_context_closed M nb nc nn HNC) as HNB.
  pose proof (source_wf_binary_left M _ _ _ SFImpl encoded body out
    ltac:(unfold sf_binary;auto) HOut HWO) as HWE.
  pose proof (source_wf_binary_left M _ _ _ SFImpl outer_all bad encoded
    ltac:(unfold sf_binary;auto) HE HWE) as HWA.
  destruct HWA as [ka [HBA _]].
  pose proof (proj1 (source_bounded_accept_unary M SFAll outer_matrix outer_all ka
    (or_introl eq_refl) HAll) HBA) as HBM.
  assert (HWM:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) outer_matrix).
  { exists (succM M ka). split;[exact HBM|apply context_bounded_empty]. }
  pose proof (source_wf_binary_left M _ _ _ SFImpl shifted closebad outer_matrix
    ltac:(unfold sf_binary;auto) HMatrix HWM) as HWS.
  pose proof (source_wf_binary_right M _ _ _ SFImpl shifted closebad outer_matrix
    ltac:(unfold sf_binary;auto) HMatrix HWM) as HWCB.
  assert (HWF:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) (zeroM M)).
  { exists (zeroM M). split;[apply source_bounded_accept_falsity|apply context_bounded_empty]. }
  destruct (sf_relation_total M SFImpl quantified (zeroM M)) as (nq&HNQ).
  pose proof (source_wf_binary M _ _ _ SFImpl quantified (zeroM M) nq
    ltac:(unfold sf_binary;auto) HNQ HWQ HWF) as HWNQ.
  destruct (environment_cons_total M nb nc nn encoded) as (eb&ec&en&HCE).
  assert (HBE:source_context_finite_bound M eb ec en).
  { apply (source_context_finite_bound_cons M nb nc nn encoded eb ec en
      (ex_intro _ (zeroM M) HNB));[|exact HCE].
    destruct HWE as [k [HK _]]. now exists k. }
  destruct (environment_cons_total M eb ec en nq) as (db&dc&dn&HCN).
  assert (HBD:source_context_finite_bound M db dc dn).
  { apply (source_context_finite_bound_cons M eb ec en nq db dc dn HBE);[|exact HCN].
    destruct HWNQ as [k [HK _]]. now exists k. }
  assert (HPQunder:source_full_prv M db dc dn quantified).
  { destruct (context_shift_total M db dc dn) as (sb&sc&HS).
    pose proof (source_context_finite_bound_shift M db dc dn sb sc HBD HS) as HBS.
    assert (HMemN:context_member M db dc dn nq).
    { apply (proj2 (context_member_cons M eb ec en nq db dc dn nq HCN)). now left. }
    destruct (context_renaming_member_forward M db dc dn (zeroM M) (zeroM M)
      (zeroM M) (succM M (zeroM M)) sb sc nq HS HMemN) as (snq&HMemSN&HRN).
    apply (proj1 (numerical_renaming_binary M SFImpl quantified (zeroM M) nq
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) snq
      ltac:(unfold sf_binary;auto) HNQ)) in HRN.
    destruct HRN as (sq&sz&HRQ&HRZ&HSN).
    assert (ESQ:sq=shifted).
    { exact (numerical_renaming_functional M quantified _ _ _ _ sq shifted HRQ HShift). }
    assert (ESZ:sz=zeroM M).
    { exact (proj1 (numerical_renaming_invalid M (zeroM M) _ _ _ _ sz (or_introl eq_refl)) HRZ). }
    subst sq sz.
    assert (HPAll:source_full_prv M db dc dn outer_all).
    { apply (full_source_AllI M db dc dn outer_matrix outer_all sb sc).
      - apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) outer_all db dc dn);[|exact HBD].
        exists ka. split;[exact HBA|apply context_bounded_empty].
      - destruct (environment_cons_total M sb sc dn shifted) as (ub&uc&un&HCS).
        assert (HBU:source_context_finite_bound M ub uc un).
        { apply (source_context_finite_bound_cons M sb sc dn shifted ub uc un HBS);[|exact HCS].
          destruct HWS as [k [HK _]]. now exists k. }
        apply (full_source_II M sb sc dn shifted closebad outer_matrix ub uc un).
        + exact (source_wf_transport_context M _ _ _ outer_matrix sb sc dn HWM HBS).
        + apply full_source_Exp.
          * exact (source_wf_transport_context M _ _ _ closebad ub uc un HWCB HBU).
          * apply (full_source_IE M ub uc un shifted (zeroM M) snq).
            -- exact (source_wf_transport_context M _ _ _ (zeroM M) ub uc un HWF HBU).
            -- apply full_source_Ctx.
               ++ apply (source_wf_binary M ub uc un SFImpl shifted (zeroM M) snq
                    ltac:(unfold sf_binary;auto) HSN).
                  ** exact (source_wf_transport_context M _ _ _ shifted ub uc un HWS HBU).
                  ** exact (source_wf_transport_context M _ _ _ (zeroM M) ub uc un HWF HBU).
               ++ apply (proj2 (context_member_cons M sb sc dn shifted ub uc un snq HCS)). now right.
            -- apply full_source_Ctx.
               ++ exact (source_wf_transport_context M _ _ _ shifted ub uc un HWS HBU).
               ++ apply (proj2 (context_member_cons M sb sc dn shifted ub uc un shifted HCS)). now left.
            -- exact HSN.
        + exact HCS.
        + exact HMatrix.
      - exact HS.
      - exact HAll. }
    assert (HPEncoded:source_full_prv M db dc dn encoded).
    { apply full_source_Ctx.
      - exact (source_wf_transport_context M _ _ _ encoded db dc dn HWE HBD).
      - apply (proj2 (context_member_cons M eb ec en nq db dc dn encoded HCN)). right.
        apply (proj2 (context_member_cons M nb nc nn encoded eb ec en encoded HCE)). now left. }
    assert (HPBad:source_full_prv M db dc dn bad).
    { apply (full_source_IE M db dc dn outer_all bad encoded);[|exact HPEncoded|exact HPAll|exact HE].
      apply (source_wf_binary_right M db dc dn SFImpl outer_all bad encoded
        ltac:(unfold sf_binary;auto) HE).
      exact (source_full_prv_wellformed M db dc dn encoded HPEncoded). }
    destruct HBD as [bound HBound].
    assert (HN':source_full_prv M db dc dn notbad).
    { apply (source_full_prv_weaken_bounded M nb nc nn db dc dn notbad bound HN);[|exact HBound].
      intros f HF. apply (proj2 (context_member_cons M eb ec en nq db dc dn f HCN)). right.
      apply (proj2 (context_member_cons M nb nc nn encoded eb ec en f HCE)). now right. }
    apply full_source_Exp.
    - exact (source_wf_transport_context M _ _ _ quantified db dc dn HWQ (ex_intro _ bound HBound)).
    - apply (full_source_IE M db dc dn bad (zeroM M) notbad);[|exact HN'|exact HPBad|exact HNot].
      exact (source_wf_transport_context M _ _ _ (zeroM M) db dc dn HWF (ex_intro _ bound HBound)). }
  destruct (sf_relation_total M SFImpl nq quantified) as (y&HY).
  destruct (sf_relation_total M SFImpl y quantified) as (pc&HPC).
  pose proof (source_wf_transport_context M _ _ _ quantified eb ec en HWQ HBE) as HWQE.
  pose proof (source_wf_transport_context M _ _ _ nq eb ec en HWNQ HBE) as HWNQE.
  pose proof (source_wf_binary M eb ec en SFImpl nq quantified y
    ltac:(unfold sf_binary;auto) HY HWNQE HWQE) as HWY.
  pose proof (full_source_II M eb ec en nq quantified y db dc dn HWY HPQunder HCN HY) as HPY.
  assert (HPQE:source_full_prv M eb ec en quantified).
  { apply (full_source_IE M eb ec en y quantified pc HWQE);[|exact HPY|exact HPC].
    apply (full_source_Pc M eb ec en quantified (zeroM M) nq y pc);[|exact HNQ|exact HY|exact HPC].
    exact (source_wf_binary M eb ec en SFImpl y quantified pc
      ltac:(unfold sf_binary;auto) HPC HWY HWQE). }
  exists nb,nc,nn. split;[exact HNC|].
  apply (full_source_II M nb nc nn encoded body out eb ec en).
  - exact (source_wf_transport_context M _ _ _ out nb nc nn HWO (ex_intro _ (zeroM M) HNB)).
  - apply (full_source_AllE M eb ec en closed quantified witness body);[|exact HPQE|exact HQ|exact HInst].
    exact (source_wf_quantifier_instance M eb ec en SFAll closed quantified witness body
      (or_introl eq_refl) HQ HWQE HInst).
  - exact HCE.
  - exact HOut.
Qed.

Print Assumptions source_zfc_vacuous_encoded_exists.
