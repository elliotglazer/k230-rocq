(** Every one of the ten fixed minimal core axioms has a checked finite
    proof of its exact current WF relativization from current core axioms. *)
From PAModel Require Import OldNamedSyntaxBridge OldFullNDSourceBridge
  SetFormulaCodes NumericalCoreAxioms SourceWFFormula SourceRelativizationCalibration
  WFClosureFiniteBridge OldWFCoreCorrespondence.
From PAModel Require OldWFFiniteAxiomImages.
From OldRegCon Require Rel.
From OldUndecidability.FOL.Sets Require minZF.
From Undecidability.FOL Require Import Syntax.Core Sets.minZF Deduction.FullND.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma old_wf_relativization_source_exact (phi:isolated_old_form OC.falsity_on) :
  isolated_formula (OldWFFiniteAxiomImages.old_wf_relativize phi)=
    sf_relativize wf_domain (isolated_formula phi).
Proof.
  unfold OldWFFiniteAxiomImages.old_wf_relativize.
  induction phi;cbn [Rel.rel isolated_formula sf_relativize].
  - reflexivity.
  - destruct P;reflexivity.
  - now rewrite IHphi1,IHphi2.
  - destruct q;cbn [Rel.rel isolated_formula sf_relativize];rewrite IHphi;
      change (isolated_formula OldWFFiniteClosure.old_wf_domain) with wf_domain;reflexivity.
Qed.

Theorem source_wf_all_fixed_finite phi : In phi Undecidability.FOL.Sets.minZF.minZFeq' ->
  exists A:list sf_form,(forall a,In a A -> standard_zfc_core_source_axiom a) /\
    @Undecidability.FOL.Deduction.FullND.prv
      Undecidability.FOL.Syntax.BinSig.sig_empty
      Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
      Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.class
      A (sf_relativize wf_domain phi).
Proof.
  intro HF. rewrite <-old_wf_core_fixed_exact in HF.
  apply List.in_map_iff in HF. destruct HF as [oldphi [<- HF]].
  destruct (OldWFFiniteAxiomImages.old_wf_minimal_fixed_images HF) as [A [HA HP]].
  exists (List.map isolated_formula A). split.
  - intros a HIn. apply List.in_map_iff in HIn. destruct HIn as [olda [<- HIn]].
    apply old_wf_minimal_core_exact,HA,HIn.
  - rewrite <-old_wf_relativization_source_exact.
    exact (@isolated_fullnd_to_current OC.falsity_on OC.class A
      (OldWFFiniteAxiomImages.old_wf_relativize oldphi) HP).
Qed.

Print Assumptions old_wf_relativization_source_exact.
Print Assumptions source_wf_all_fixed_finite.
