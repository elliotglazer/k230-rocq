(** Foundation holds in the WF domain by pure source first-order reasoning.
    This is the exact fixed Foundation axiom used by the numerical source. *)
From PAModel Require Import SetFormulaCodes ZFCFiniteAxiomTemplates
  SourceWFFormula SourceRelativizationCalibration.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Undecidability Require Import Shared.ListAutomation.
From Stdlib Require Import Lists.List.
Import ListAutomationNotations ListAutomationHints.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Hint Constructors prv : core.
#[local] Instance wf_foundation_pc : peirce := class.

Theorem wf_foundation_image_prv (G:list sf_form) :
  G ⊢ sf_relativize wf_domain source_foundation.
Proof.
  unfold source_foundation. cbn [sf_relativize].
  apply AllI_named. intros x. wf_simp. apply II,II.
  eapply ExE_named;[apply Ctx;cbn;tauto|]. intros y. wf_simp.
  apply wf_source_conjunction_split.
  apply (wf_source_class_elim (x:=x));[apply Ctx;cbn;tauto|]. intros t.
  eapply wf_source_minimal_elim with (s:=x).
  - eapply wf_source_wellf_elim with (t:=t) (s:=x) (w:=y).
    + eapply wf_source_tw_wellf;apply Ctx;cbn;tauto.
    + apply wf_source_subset_intro. intros z.
      eapply wf_source_transitive_elim with (x:=t) (y:=x) (z:=z).
      * eapply wf_source_tw_transitive;apply Ctx;cbn;tauto.
      * apply Ctx;cbn;tauto.
      * apply Ctx;cbn;tauto.
    + apply Ctx;cbn;tauto.
  - intros m. apply (ExI m). wf_simp. apply CI;[|apply CI].
    + eapply wf_source_member with (x:=x) (y:=m);[apply Ctx;cbn;tauto|].
      eapply wf_source_minel_member with (m:=m) (s:=x);apply Ctx;cbn;tauto.
    + eapply wf_source_minel_member with (m:=m) (s:=x);apply Ctx;cbn;tauto.
    + apply AllI_named. intros z. wf_simp. apply II,II,II.
      eapply wf_source_minel_disjoint with (m:=m) (s:=x) (z:=z);apply Ctx;cbn;tauto.
Qed.

Print Assumptions wf_foundation_image_prv.




