From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SetCodeDescent
  SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalInstantiation SourceSequents SourceTraceBounds SourceContextTransport
  SourceInstantiationConstructors SourceQuantifierRules NumericalSourceFull SourceProofWeakening
  SourceClosedContextShift SourceUniversalPropositional SourceExistentialShift SourceImplicationAllShift
  SourceZFCProvability SourceZFCRenaming SourceZFCPrograms.
Unset Implicit Arguments.

Theorem source_zfc_implies_all M a b alla allb k :
  source_bounded M a k ->source_bounded M b k ->source_zfc_implies M a b ->
  sf_relation M SFAll a (zeroM M) alla ->sf_relation M SFAll b (zeroM M) allb ->
  source_zfc_implies M alla allb.
Proof.
  intros HA HB HI HAlla HAllb out HOut.
  destruct (sf_relation_total M SFImpl a b) as (imp&HImp).
  destruct (HI imp HImp) as (cb&cc&cn&HC&PI).
  pose proof (source_zfc_context_closed M cb cc cn HC) as HCB.
  assert (HWA:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) alla).
  { exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_unary M SFAll a alla k (or_introl eq_refl) HAlla)).
    exact (source_bounded_monotone M a k (succM M k) HA
      (coding_lt_trans M k _ _ (coding_lt_succ M k) (coding_lt_succ M (succM M k)))). }
  assert (HWB:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) allb).
  { exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_unary M SFAll b allb k (or_introl eq_refl) HAllb)).
    exact (source_bounded_monotone M b k (succM M k) HB
      (coding_lt_trans M k _ _ (coding_lt_succ M k) (coding_lt_succ M (succM M k)))). }
  destruct (environment_cons_total M cb cc cn alla) as (u&v&l&HCons).
  assert (HBound:source_context_finite_bound M u v l).
  { apply (source_context_finite_bound_cons M cb cc cn alla u v l
      (ex_intro _ (zeroM M) HCB));[|exact HCons].
    destruct HWA as [q [HQ _]]. now exists q. }
  destruct (context_shift_total M u v l) as (s&t&HShift).
  pose proof (source_context_finite_bound_shift M u v l s t HBound HShift) as HSBound.
  assert (PI':source_full_prv M s t l imp).
  { destruct HSBound as [q HQ].
    apply (source_full_prv_weaken_bounded M cb cc cn s t l imp q PI);[|exact HQ].
    apply (source_context_included_shift M cb cc cn u v l cb cc s t).
    - intros f HF. apply (proj2 (context_member_cons M cb cc cn alla u v l f HCons)). now right.
    - exact (source_closed_context_shift_self M cb cc cn HCB).
    - exact HShift. }
  exists cb,cc,cn. split;[exact HC|].
  apply (full_source_II M cb cc cn alla allb out u v l).
  - apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) out cb cc cn);[|now exists (zeroM M)].
    exact (source_wf_binary M _ _ _ SFImpl alla allb out
      ltac:(unfold sf_binary;auto) HOut HWA HWB).
  - apply (source_full_universal_map M u v l a b alla allb imp s t).
    + exact (source_wf_transport_context M _ _ _ allb u v l HWB HBound).
    + exact HAlla.
    + exact HAllb.
    + exact HImp.
    + exact HShift.
    + apply full_source_Ctx.
      * exact (source_wf_transport_context M _ _ _ alla u v l HWA HBound).
      * apply (proj2 (context_member_cons M cb cc cn alla u v l alla HCons)). now left.
    + exact PI'.
  - exact HCons.
  - exact HOut.
Qed.

Theorem source_zfc_implies_ex M a b exa exb k :
  source_bounded M a k ->source_bounded M b k ->source_zfc_implies M a b ->
  sf_relation M SFEx a (zeroM M) exa ->sf_relation M SFEx b (zeroM M) exb ->
  source_zfc_implies M exa exb.
Proof.
  intros HA HB HI HExa HExb out HOut.
  destruct (sf_relation_total M SFImpl a b) as (imp&HImp).
  destruct (HI imp HImp) as (cb&cc&cn&HC&PI).
  pose proof (source_zfc_context_closed M cb cc cn HC) as HCB.
  assert (HWA:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) exa).
  { exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_unary M SFEx a exa k (or_intror eq_refl) HExa)).
    exact (source_bounded_monotone M a k (succM M k) HA
      (coding_lt_trans M k _ _ (coding_lt_succ M k) (coding_lt_succ M (succM M k)))). }
  assert (HWB:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) exb).
  { exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_unary M SFEx b exb k (or_intror eq_refl) HExb)).
    exact (source_bounded_monotone M b k (succM M k) HB
      (coding_lt_trans M k _ _ (coding_lt_succ M k) (coding_lt_succ M (succM M k)))). }
  destruct (environment_cons_total M cb cc cn exa) as (u&v&l&HCons).
  assert (HBound:source_context_finite_bound M u v l).
  { apply (source_context_finite_bound_cons M cb cc cn exa u v l
      (ex_intro _ (zeroM M) HCB));[|exact HCons].
    destruct HWA as [q [HQ _]]. now exists q. }
  destruct (context_shift_total M u v l) as (s&t&HShift).
  pose proof (source_context_finite_bound_shift M u v l s t HBound HShift) as HSBound.
  destruct (environment_cons_total M s t l a) as (d&e&m&HACons).
  pose proof (source_context_finite_bound_cons M s t l a d e m HSBound (ex_intro _ k HA) HACons) as HDBound.
  destruct (numerical_renaming_total M exb (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as (shifted&HShiftEx).
  destruct (source_shifted_ex_specialization M b exb shifted k HB HExb HShiftEx) as (br&HExShift&HInst).
  assert (HWShift:source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) shifted).
  { destruct HWB as [q [HQ _]]. exists (succM M q). split;[|apply context_bounded_empty].
    exact (source_shift_bound M exb shifted q HQ HShiftEx). }
  assert (PI':source_full_prv M d e m imp).
  { destruct HDBound as [q HQ].
    apply (source_full_prv_weaken_bounded M cb cc cn d e m imp q PI);[|exact HQ].
    intros f HF. apply (proj2 (context_member_cons M s t l a d e m f HACons)). right.
    apply (source_context_included_shift M cb cc cn u v l cb cc s t).
    - intros g HG. apply (proj2 (context_member_cons M cb cc cn exa u v l g HCons)). now right.
    - exact (source_closed_context_shift_self M cb cc cn HCB).
    - exact HShift.
    - exact HF. }
  exists cb,cc,cn. split;[exact HC|].
  apply (full_source_II M cb cc cn exa exb out u v l).
  - apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) out cb cc cn);[|now exists (zeroM M)].
    exact (source_wf_binary M _ _ _ SFImpl exa exb out ltac:(unfold sf_binary;auto) HOut HWA HWB).
  - apply (full_source_ExE M u v l a exa exb shifted s t d e m).
    + exact (source_wf_transport_context M _ _ _ exb u v l HWB HBound).
    + apply full_source_Ctx.
      * exact (source_wf_transport_context M _ _ _ exa u v l HWA HBound).
      * apply (proj2 (context_member_cons M cb cc cn exa u v l exa HCons)). now left.
    + apply (full_source_ExI M d e m br shifted (zeroM M) b).
      * exact (source_wf_transport_context M _ _ _ shifted d e m HWShift HDBound).
      * apply (full_source_IE M d e m a b imp).
        -- apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) b d e m);[|exact HDBound].
           exists k. split;[exact HB|apply context_bounded_empty].
        -- exact PI'.
        -- apply full_source_Ctx.
           ++ apply (source_wf_transport_context M (zeroM M) (zeroM M) (zeroM M) a d e m);[|exact HDBound].
              exists k. split;[exact HA|apply context_bounded_empty].
           ++ apply (proj2 (context_member_cons M s t l a d e m a HACons)). now left.
        -- exact HImp.
      * exact HExShift.
      * exact HInst.
    + exact HExa.
    + exact HShift.
    + exact HACons.
    + exact HShiftEx.
  - exact HCons.
  - exact HOut.
Qed.

Theorem source_zfc_equivalent_quantifier M h a b qa qb k :
  (h=SFAll \/h=SFEx) ->source_bounded M a k ->source_bounded M b k ->
  source_zfc_equivalent M a b ->sf_relation M h a (zeroM M) qa ->
  sf_relation M h b (zeroM M) qb ->source_zfc_equivalent M qa qb.
Proof.
  intros [EH|EH] HA HB [HI HR] HQA HQB;subst h;split.
  - exact (source_zfc_implies_all M a b qa qb k HA HB HI HQA HQB).
  - exact (source_zfc_implies_all M b a qb qa k HB HA HR HQB HQA).
  - exact (source_zfc_implies_ex M a b qa qb k HA HB HI HQA HQB).
  - exact (source_zfc_implies_ex M b a qb qa k HB HA HR HQB HQA).
Qed.

Theorem source_zfc_equivalent_renaming M a b rb rc rn delta ar br :
  source_zfc_equivalent M a b ->numerical_renaming M a rb rc rn delta ar ->
  numerical_renaming M b rb rc rn delta br ->source_zfc_equivalent M ar br.
Proof.
  intros [HI HR] HA HB.
  assert (Transport:forall a b ar br,source_zfc_implies M a b ->
      numerical_renaming M a rb rc rn delta ar ->numerical_renaming M b rb rc rn delta br ->
      source_zfc_implies M ar br).
  { intros f g fr gr HFG HF HG out HOut.
    destruct (sf_relation_total M SFImpl f g) as (imp&HImp).
    apply (source_zfc_provable_renaming M imp rb rc rn delta out (HFG imp HImp)).
    apply (proj2 (numerical_renaming_binary M SFImpl f g imp rb rc rn delta out
      ltac:(unfold sf_binary;auto) HImp)). exists fr,gr. auto. }
  split;[exact (Transport a b ar br HI HA HB)|exact (Transport b a br ar HR HB HA)].
Qed.

Print Assumptions source_zfc_equivalent_quantifier.
Print Assumptions source_zfc_equivalent_renaming.
