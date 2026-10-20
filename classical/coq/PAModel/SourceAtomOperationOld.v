(** Actual atomic Op6/Op7 profile laws. The environment, its index
 values and assignment values are independent free roles. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld SourceAtomLookupOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Lemma old_atom_operation_lookup {G:list form}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)
 (member:bool) e xi xj a b An R:
 G ⊢C Op(if member then 6 else 7)An xi xj R ->G ⊢C e ∈' An ->
 G ⊢C old_atom_app_profile e xi a ->G ⊢C old_atom_app_profile e xj b ->
 G ⊢C (e ∈' R ↔if member then a ∈' b else a ≡' b).
Proof.
 intros HOp HE HL HRi. destruct member.
 - fhave D:(sepof_iff HG An R _ HOp). finst D e.
   fhave I:(old_atom_ai_lookup HG HR HOm HC e xi xj a b HL HRi). fsplit.
   + fintro H. exact(iff_l _ _ _ I(CE2(iff_l _ _ _ D H))).
   + fintro H. apply(iff_r _ _ _ D). fsplit;[exact HE|exact(iff_r _ _ _ I H)].
 - fhave D:(sepof_iff HG An R _ HOp). finst D e.
   fhave I:(old_atom_ae_lookup HG HR HOm HC e xi xj a b HL HRi). fsplit.
   + fintro H. exact(iff_l _ _ _ I(CE2(iff_l _ _ _ D H))).
   + fintro H. apply(iff_r _ _ _ D). fsplit;[exact HE|exact(iff_r _ _ _ I H)].
Qed.
Definition old_atom_operation_law(member:bool):form:=
 Op(if member then 6 else 7)$5 $1 $2 $6 →$0 ∈' $5 →
 old_atom_app_profile $0 $1 $3 →old_atom_app_profile $0 $2 $4 →
 ($0 ∈' $6 ↔if member then $3 ∈' $4 else $3 ≡' $4).
Theorem old_atom_operation_proof member:old_L_background ⊢C old_atom_operation_law member.
Proof.
 unfold old_atom_operation_law. do 4 apply II.
 eapply old_atom_operation_lookup with(member:=member)(e:=$0)(xi:=$1)(xj:=$2)(a:=$3)(b:=$4)(An:=$5)(R:=$6).
 - intros ax H. do 4 right. exact(old_hierarchy_base ax H).
 - do 4 right. exact old_hierarchy_reg.
 - do 4 right. exact old_hierarchy_omega.
 - intros ax H. do 4 right. exact(old_closure_axioms ax H).
 - apply Ctx. do 3 right. now left.
 - apply Ctx. do 2 right. now left.
 - apply Ctx. right. now left.
 - apply Ctx. now left.
Qed.
Print Assumptions old_atom_operation_proof.
