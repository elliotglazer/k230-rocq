(** A fixed strengthening of L_bound: the covering level itself is in L.
    Both original finite hierarchy theorems are used in the real source calculus. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_L Z_axL.
From PAModel Require Import SourceLFixed SourceLBoundOld SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Definition old_L_element_bound_law:form:=
 ∃(InL $0 ∧∀($0 ∈' $2 →InL $0 →$0 ∈' $1)).
Theorem old_L_element_bound_proof:old_L_bound_background ⊢C old_L_element_bound_law.
Proof.
 assert(HG:incl ZF0base old_L_bound_background).
 { intros a HA. apply in_app_iff. left;exact(old_hierarchy_base a HA). }
 assert(HR:In ax_reg' old_L_bound_background).
 { apply in_app_iff. left;exact old_hierarchy_reg. }
 assert(HOm:In ax_om' old_L_bound_background).
 { apply in_app_iff. left;exact old_hierarchy_omega. }
 assert(HL:incl Ax_L old_L_bound_background).
 { intros a HA. apply in_app_iff. left;exact(old_hierarchy_axioms a HA). }
 pose proof old_L_bound_proof as HBound.
 unfold old_L_bound_law in HBound. unfold old_L_element_bound_law.
 fex HBound ordinal HOrdinalWitness.
 fex HOrdinalWitness Y HLevelWitness.
 fdestr HLevelWitness HPair HCover. fdestr HPair HOrdinal HLevel.
 fexists Y. fsplit;[|exact HCover].
 eapply L_LL_g with(a:=ordinal)(Y:=Y);eassumption.
Qed.
Print Assumptions old_L_element_bound_proof.
