(** Consume a native closed image through an actual source ZFC
    normalization proof. Different prefix lengths are allowed: the native
    closure is first eliminated inside the source proof, then the genuine
    raw-source closure is introduced. Relative transfer discharges the
    internally bounded domain table using actual domain nonemptiness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalTheories
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundedCalibration NumericalSetClosure NumericalContexts
  NumericalEnvironments NumericalSourceFull SourceSequents SourceTraceBounds SourceContextTransport
  SourceProofWeakening SourceInstantiationConstructors SourceClosedPrefixes
  SourceZFCProvability SourceSetTheoryDescriptors SourceAxiomContexts SourceContextImages
  SourceImageContextWitnesses SourceDescriptorProvability SourceDescriptorRelativeTransfer
  SourceRelativeTheoryTransfer SourceRelativization SourceRelativizationBounds.
Unset Implicit Arguments.

Theorem source_relative_closed_normalization M T domain ex native raw n m closed_native closed_raw
    relative_native relative_raw imp :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor T domain ->
  source_bounded M closed_native (zeroM M) ->source_bounded M closed_raw (zeroM M) ->
  all_prefix M m native closed_native ->all_prefix M n raw closed_raw ->
  sf_relation M SFImpl native raw imp ->source_zfc_provable M imp ->
  source_relativization M domain closed_native relative_native ->
  source_descriptor_provable M T relative_native ->
  source_relativization M domain closed_raw relative_raw ->
  source_descriptor_provable M T relative_raw.
Proof.
  intros HD HEx (eb&ec&en&HE&PE) HImages HNClosed HRClosed HNPrefix HRPrefix
    HImp (b&c&l&HC&PI) HRelN (nb&nc&nn&HNC&PN) HRelR.
  pose proof (source_zfc_context_closed M b c l HC) as HB.
  destruct (environment_cons_total M b c l closed_native) as (sb&sc&sn&HCons).
  assert (HClosed:context_bounded M sb sc sn (zeroM M)).
  { apply (proj2 (context_bounded_cons M b c l closed_native sb sc sn (zeroM M) HCons)). auto. }
  assert (PI':source_full_prv M sb sc sn imp).
  { apply (source_full_prv_weaken_bounded M b c l sb sc sn imp (zeroM M) PI);[|exact HClosed].
    intros f HF. apply (proj2 (context_member_cons M b c l closed_native sb sc sn f HCons)). now right. }
  assert (PNative:source_full_prv M sb sc sn native).
  { apply (source_full_prefix_eliminate M sb sc sn m native closed_native HClosed HNPrefix).
    apply full_source_Ctx.
    - exists (zeroM M). auto.
    - apply (proj2 (context_member_cons M b c l closed_native sb sc sn closed_native HCons)). now left. }
  assert (PRaw:source_full_prv M sb sc sn raw).
  { apply (full_source_IE M sb sc sn native raw imp);[|exact PI'|exact PNative|exact HImp].
    exact (source_wf_binary_right M sb sc sn SFImpl native raw imp
      ltac:(unfold sf_binary;auto) HImp (source_full_prv_wellformed M sb sc sn imp PI')). }
  pose proof (source_full_prefix_introduce M sb sc sn n raw closed_raw HClosed HRPrefix PRaw) as PClosedRaw.
  destruct (source_axiom_image_context_collect_witnesses_with_proof M T domain sb sc sn
    eb ec en ex HE PE) as (ub&uc&un&HUC&PUEx&HContextImages).
  - intros f HF. apply (proj1 (context_member_cons M b c l closed_native sb sc sn f HCons)) in HF.
    destruct HF as [<-|HF].
    + exists relative_native,nb,nc,nn. auto.
    + destruct (HImages f (proj2 (ZFCSourceDescriptor_axiom M f) (HC f HF)) (HB f HF))
        as (rf&HR&rb&rc&rn&HRC&PR).
      exists rf,rb,rc,rn. auto.
  - exists ub,uc,un. split;[exact HUC|].
    apply (source_relative_proof_transfer M domain ex ub uc un sb sc sn closed_raw relative_raw
      (proj1 HUC) HD HEx PUEx).
    + exact (source_relativization_preserves_bound M closed_raw domain (zeroM M) relative_raw HD HRClosed HRelR).
    + exact HRelR.
    + exact HContextImages.
    + exact PClosedRaw.
Qed.

Print Assumptions source_relative_closed_normalization.
