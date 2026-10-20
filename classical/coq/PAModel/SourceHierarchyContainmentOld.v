(** Literal finite containment in L; the ordinal guard is essential. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd.
From OldZFC Require Import Z_base Z_L.
From PAModel Require Import SourceLFixed.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
Definition old_hierarchy_containment_law:form:=
 Ord0 $0 →LL $0 $1 →$2 ∈' $1 →InL $2.
Theorem old_hierarchy_containment_proof:old_L_background ⊢C old_hierarchy_containment_law.
Proof.
 unfold old_hierarchy_containment_law. do 3 apply II.
 apply(InL_intro $0 $1 $2).
 - apply Ctx. do 2 right. now left.
 - apply Ctx. right. now left.
 - apply Ctx. now left.
Qed.
Print Assumptions old_hierarchy_containment_proof.

Definition old_hierarchy_carrier_law:form:=
 Ord0 $0 →LL $0 $1 →∀($0 ∈' $2 →InL $0).
Theorem old_hierarchy_carrier_proof:old_L_background ⊢C old_hierarchy_carrier_law.
Proof.
 unfold old_hierarchy_carrier_law. do 2 apply II. apply AllI. apply II.
 apply(InL_intro $1 $2 $0).
 - apply Ctx. right. cbn [List.map]. right. left. autorewrite with fsub. reflexivity.
 - apply Ctx. right. cbn [List.map]. left. autorewrite with fsub. reflexivity.
 - apply Ctx. now left.
Qed.
Print Assumptions old_hierarchy_carrier_proof.
