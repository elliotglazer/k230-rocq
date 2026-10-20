(** All twelve fixed ZFC axioms hold in the exact pinned L interpretation,
    with actual numerical ZFR proofs in every PA model. Separation and
    Replacement at arbitrary internal matrices are not asserted here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge OldZFRProofLift OldRelativizationBridge
  SourceLFixed SourceLNonempty SourceZFRProvability
  SourceRelativization SourceRelativizationCalibration SourceRelativizationFunctionality
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes SourceNumeralLift.
From OldZFC Require Z_prim Z_L Z_axL Z_ac Z_wo.
From OldZF Require Std_iface.
From OldRegCon Require Rel MinZF.
From OldUndecidability.FOL.Sets Require minZF.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition old_L_image (phi:isolated_old_form OC.falsity_on) :=
  @OldRegCon.Rel.rel OldUndecidability.FOL.Syntax.BinSig.sig_empty
    OS.ZFSignature.ZF_pred_sig OldZFC.Z_L.Lform OC.falsity_on phi.

Lemma old_L_background_base A :
  incl OldZF.Std_iface.ZF0base (old_L_background++A).
Proof.
  intros a HA. apply in_app_iff. left. unfold old_L_background.
  right;right. apply in_app_iff. now left.
Qed.
Lemma old_L_background_reg A : In OldRegCon.MinZF.ax_reg' (old_L_background++A).
Proof. apply in_app_iff. left. now left. Qed.
Lemma old_L_background_omega A :
  In OldUndecidability.FOL.Sets.minZF.ax_om' (old_L_background++A).
Proof. apply in_app_iff. left. right;now left. Qed.
Lemma old_L_background_hierarchy A : incl OldZFC.Z_L.Ax_L (old_L_background++A).
Proof.
  intros a HA. apply in_app_iff. left. unfold old_L_background.
  right;right. apply in_app_iff. now right.
Qed.
Lemma old_L_extended_background_valid A :
  (forall a,In a A -> OldZFC.Z_prim.ZFR a) ->
  forall a,In a (old_L_background++A) -> OldZFC.Z_prim.ZFR a.
Proof.
  intros HA a H. apply in_app_iff in H as [H|H].
  - exact (old_L_background_valid a H).
  - exact (HA a H).
Qed.

Theorem old_L_zfr_axiom_finite phi : OldZFC.Z_prim.ZFR phi ->
  exists A,(forall a,In a A -> OldZFC.Z_prim.ZFR a) /\
    @OND.prv OldUndecidability.FOL.Syntax.BinSig.sig_empty
      OS.ZFSignature.ZF_pred_sig OC.falsity_on OC.class A (old_L_image phi).
Proof.
  intro H. destruct (OldZFC.Z_axL.axL_ZFR phi H) as [A [HA HP]].
  exists (old_L_background++A). split.
  - exact (old_L_extended_background_valid A HA).
  - apply HP.
    + apply old_L_background_base.
    + apply old_L_background_reg.
    + apply old_L_background_omega.
    + apply old_L_background_hierarchy.
    + intros a HIn. apply in_app_iff. now right.
Qed.

Theorem old_L_choice_finite :
  exists A,(forall a,In a A -> OldZFC.Z_prim.ZFR a) /\
    @OND.prv OldUndecidability.FOL.Syntax.BinSig.sig_empty
      OS.ZFSignature.ZF_pred_sig OC.falsity_on OC.class A
      (old_L_image OldZFC.Z_wo.ax_ac).
Proof.
  destruct OldZFC.Z_ac.acL_ex as [A [HA HP]].
  exists (old_L_background++A). split.
  - exact (old_L_extended_background_valid A HA).
  - apply HP.
    + apply old_L_background_base.
    + apply old_L_background_reg.
    + apply old_L_background_omega.
    + apply old_L_background_hierarchy.
    + intros a HIn. apply in_app_iff. now right.
Qed.

Definition old_fixed_zfc_source (tag:zfc_fixed_axiom) : isolated_old_form OC.falsity_on :=
  match tag with
  | ZFCRefl => OldUndecidability.FOL.Sets.minZF.ax_refl'
  | ZFCSym => OldUndecidability.FOL.Sets.minZF.ax_sym'
  | ZFCTrans => OldUndecidability.FOL.Sets.minZF.ax_trans'
  | ZFCEqElem => OldUndecidability.FOL.Sets.minZF.ax_eq_elem'
  | ZFCExt => OldUndecidability.FOL.Sets.minZF.ax_ext'
  | ZFCEmpty => OldUndecidability.FOL.Sets.minZF.ax_eset'
  | ZFCPair => OldUndecidability.FOL.Sets.minZF.ax_pair'
  | ZFCUnion => OldUndecidability.FOL.Sets.minZF.ax_union'
  | ZFCPower => OldUndecidability.FOL.Sets.minZF.ax_power'
  | ZFCOmega => OldUndecidability.FOL.Sets.minZF.ax_om'
  | ZFCFoundation => OldRegCon.MinZF.ax_reg'
  | ZFCChoice => OldZFC.Z_wo.ax_ac
  end.

Lemma old_fixed_zfc_source_exact tag :
  isolated_formula (old_fixed_zfc_source tag)=zfc_fixed_source tag.
Proof. destruct tag;reflexivity. Qed.

Lemma old_fixed_zfc_source_zfr tag : tag<>ZFCChoice ->
  OldZFC.Z_prim.ZFR (old_fixed_zfc_source tag).
Proof.
  destruct tag;intro H;cbn [old_fixed_zfc_source].
  all: try (left;left;apply OldZF.Std_iface.ZF0_base;
    cbn [OldZF.Std_iface.ZF0base List.In];tauto).
  - left;right. reflexivity.
  - right. reflexivity.
Qed.

Theorem finite_L_fixed_axiom_zfr M tag :
  source_zfr_provable M
    (code_numeral M (sf_encode (sf_relativize source_L_domain (zfc_fixed_source tag)))).
Proof.
  assert (HF:exists A,(forall a,In a A -> OldZFC.Z_prim.ZFR a) /\
    @OND.prv OldUndecidability.FOL.Syntax.BinSig.sig_empty
      OS.ZFSignature.ZF_pred_sig OC.falsity_on OC.class A
      (old_L_image (old_fixed_zfc_source tag))).
  { destruct tag.
    all: try (apply old_L_zfr_axiom_finite,old_fixed_zfc_source_zfr;discriminate).
    exact old_L_choice_finite. }
  destruct HF as [A [HA HP]].
  pose proof (finite_old_zfr_proof_lift M A _ HA HP) as H.
  unfold old_L_image in H.
  rewrite isolated_relativization,old_fixed_zfc_source_exact in H.
  exact H.
Qed.

Theorem numerical_L_fixed_axiom_images M tag f rf :
  zfc_source_graph M tag f ->
  source_relativization M (source_L_domain_code M) f rf ->
  source_zfr_provable M rf.
Proof.
  intros HF HR.
  pose proof (zfc_source_graph_functional M tag f
    (code_numeral M (sf_encode (zfc_fixed_source tag))) HF
    (source_formula_numeral_graph M (zfc_fixed_source tag))) as EF. subst f.
  pose proof (source_relativization_finite_lift M source_L_domain (zfc_fixed_source tag)) as HR0.
  pose proof (source_relativization_functional M (code_numeral M (sf_encode (zfc_fixed_source tag)))
    (source_L_domain_code M) rf
    (code_numeral M (sf_encode (sf_relativize source_L_domain (zfc_fixed_source tag)))) HR HR0) as ER.
  subst rf. apply finite_L_fixed_axiom_zfr.
Qed.

Print Assumptions old_L_zfr_axiom_finite.
Print Assumptions old_L_choice_finite.
Print Assumptions old_fixed_zfc_source_exact.
Print Assumptions old_fixed_zfc_source_zfr.
Print Assumptions finite_L_fixed_axiom_zfr.
Print Assumptions numerical_L_fixed_axiom_images.
