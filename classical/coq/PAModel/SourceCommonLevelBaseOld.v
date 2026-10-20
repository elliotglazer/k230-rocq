(** A fixed hierarchy witness for the zero-parameter common-level base. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_common_level_empty :form :=
  ∃(∃((Ord0 $1 ∧LL $1 $0) ∧(⊥→⊥))).
Theorem old_common_level_empty_proof :old_L_background ⊢C old_common_level_empty.
Proof.
  assert (HG:incl ZF0base old_L_background) by exact old_hierarchy_base.
  assert (HR:In ax_reg' old_L_background) by exact old_hierarchy_reg.
  assert (HOm:In ax_om' old_L_background) by exact old_hierarchy_omega.
  assert (HL:incl Ax_L old_L_background) by exact old_hierarchy_axioms.
  unfold old_common_level_empty.
  pose proof (emp0_ex HG) as HE. apply (ExE_named HE). intro e.
  set (G1:=(Emp0 $0)[e..]::old_L_background).
  assert (HG1:incl ZF0base G1) by (intros a HA;right;exact (HG a HA)).
  assert (HR1:In ax_reg' G1) by (right;exact HR).
  assert (HO1:In ax_om' G1) by (right;exact HOm).
  assert (HL1:incl Ax_L G1) by (intros a HA;right;exact (HL a HA)).
  assert (PE:G1 ⊢C Emp0 e).
  { change (((Emp0 $0)[e..]::old_L_background) ⊢C Emp0 e).
    replace (Emp0 e) with ((Emp0 $0)[e..]) by (simp;reflexivity). apply Ctx. now left. }
  pose proof (ord_emp_g e PE) as PO.
  pose proof (LL_ex_g HG1 HR1 HO1 HL1 e PO) as HY.
  apply (ExE_named HY). intro Y.
  fexists e. fexists Y. fsplit.
  - fsplit.
    + eapply weak_cons. exact PO.
    + replace (LL e Y) with ((LL e`[↑] $0)[Y..]) by (simp;reflexivity). apply Ctx. now left.
  - apply II,Ctx. now left.
Qed.
Print Assumptions old_common_level_empty_proof.
