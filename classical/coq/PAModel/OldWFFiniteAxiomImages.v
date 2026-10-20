(** All ten fixed minimal core axioms have actual finite WF image proofs.
    The original rich-signature machinery is used only to obtain these ten
    fixed derivations; it is not applied to arbitrary internally coded proofs. *)
From OldUndecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts.
From OldUndecidability.FOL.Sets Require Import ZF minZF.
From OldUndecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_minZF PCPb_to_ZFD.
From OldUndecidability.FOL.Sets.Models Require Import ZF_conservativity.
From OldUndecidability Require Import Shared.ListAutomation.
From OldRegCon Require Import Rel WF Main MinZF.
From PAModel Require Import OldWFFiniteClosure.
From Stdlib Require Import Lists.List Lia.
Import ListAutomationNotations ListAutomationHints.
Open Scope syn.
Set Implicit Arguments.
#[local] Instance old_wf_images_pc : peirce := class.
#[local] Hint Constructors prv : core.
#[local] Instance old_wf_image_func_dec : eq_dec ZF_func_sig.
Proof. intros x y. unfold dec. decide equality. Defined.
#[local] Instance old_wf_image_pred_dec : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

Definition old_wf_relativize (phi:old_wf_form) := Rel.rel old_wf_domain phi.

Lemma old_wf_embed_relativize (phi:old_wf_form) :
  embed (old_wf_relativize phi)=Rel.rel Mwf (embed phi).
Proof.
  unfold old_wf_relativize. induction phi;cbn [Rel.rel embed].
  - reflexivity.
  - reflexivity.
  - now rewrite IHphi1,IHphi2.
  - destruct q;cbn [Rel.rel embed];rewrite IHphi;reflexivity.
Qed.

Lemma old_wf_rich_base_image a : In a ZFeq' -> B0 ⊢ Rel.rel Mwf a.
Proof.
  intro HA. assert (HB:B0 <<= B0) by auto.
  pose proof (B0_ZFeq HB) as HT.
  unfold ZFeq',ZF' in HA. repeat (destruct HA as [<-|HA]);try destruct HA.
  1-4,6-7: apply rel_qf;[exact HT|cbn;tauto].
  - now apply rel_ext.
  - now apply rel_union.
  - now apply rel_power.
  - now apply rel_om1.
  - now apply rel_om2.
Qed.

Lemma old_wf_embedded_fixed_closed (phi:old_wf_form) :
  In phi minZFeq' -> bounded 0 (embed phi).
Proof.
  intro HA. unfold minZFeq',minZF' in HA.
  repeat (destruct HA as [<-|HA];
    [apply (proj1 (bounded_comp_eq 0 _));compute;repeat split;lia|]).
  destruct HA.
Qed.

Lemma old_wf_rich_minimal_fixed_image (phi:old_wf_form) :
  In phi minZFeq' -> B0 ⊢ embed (old_wf_relativize phi).
Proof.
  intro HF. rewrite old_wf_embed_relativize.
  pose proof (embed_ZF' HF) as HP.
  pose proof (rel_prv Mwf_bounded (p0:=class) B0_closed Mwf_funcs HP
    (Gamma:=B0) (sigma:=fun _=>∅)) as HR.
  rewrite (rel_closed Mwf_bounded (phi:=embed phi)) in HR.
  - apply HR.
    + auto.
    + intros k. rewrite Mwf_inst. apply WF_eset.
      * apply B0_ZFeq;auto.
      * apply B0_Wax;auto.
    + intros a HA. rewrite (rel_closed Mwf_bounded).
      * now apply old_wf_rich_base_image.
      * apply (ZFcReg_closed (ZFcReg_ZF (ZFc_base HA))).
  - now apply old_wf_embedded_fixed_closed.
Qed.

Lemma old_wf_rich_fixed_finite_transfer (phi:old_wf_form) :
  B0 ⊢ embed phi ->
  exists A:list old_wf_form,(forall a,In a A -> ZFcl_min a) /\ A ⊢ phi.
Proof.
  intro HP.
  assert (HP':(B0 ++ ZFeq') ⊢ embed phi) by (apply (Weak HP);auto).
  apply rm_const_prv in HP'.
  destruct (collect (R:=fun L (a:form)=>L ⊢ rm_const_fm a) (Q:=ZFcl_min) (A:=B0))
    as [L [HL HPr]].
  - intros A B x HX HAB. exact (Weak HX HAB).
  - intros a HA. now apply rm_const_axiom,old_B0_is_core.
  - exists (L ++ minZFeq'). split.
    + intros a HA. apply in_app_iff in HA. destruct HA as [HA|HA];[now apply HL|now left].
    + apply loop_deductive';[auto|].
      apply (prv_cut HP'). intros a HA. apply in_app_iff in HA. destruct HA as [HA|HA].
      * apply in_map_iff in HA. destruct HA as [theta [<- HIn]].
        apply (Weak (HPr theta HIn));auto.
      * apply Ctx. apply in_app_iff. now right.
Qed.

Theorem old_wf_minimal_fixed_images phi : In phi minZFeq' ->
  exists A:list old_wf_form,(forall a,In a A -> ZFcl_min a) /\ A ⊢ old_wf_relativize phi.
Proof. intro HF. apply old_wf_rich_fixed_finite_transfer,old_wf_rich_minimal_fixed_image,HF. Qed.

Print Assumptions old_wf_embed_relativize.
Print Assumptions old_wf_rich_minimal_fixed_image.
Print Assumptions old_wf_minimal_fixed_images.
