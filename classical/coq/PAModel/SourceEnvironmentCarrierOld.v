(** Fixed mathematical base and step laws for carriers of environments.
    No induction over an environment length occurs in this finite module. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.

Lemma old_environment_carrier_zero {G:list form}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)
 A S0 C :G ⊢C Succ0 A S0 ->G ⊢C Cl S0 C ->
 G ⊢C ∃($0 ∈' C`[↑] ∧∀(Emp0 $0 →$0 ∈' $1)).
Proof.
 intros HS HCl. fobtain(cl_emp HG HR HOm HC A S0 C HS HCl)as e0 HE0. fdestr HE0 HEmp HIn.
 fobtain(cl_op_g HG HR HOm HC 0 S0 C e0 e0 e0 ltac:(lia)HCl HIn HIn HIn)as R HRep.
 fdestr HRep HRC HPair. fexists R. fsplit;[exact HRC|]. fall e. fintro HE.
 fhave E:(u_emp0_unique HG HR HOm HC e e0 HE HEmp).
 fhave H:(pair0_l HG e0 e0 R HPair). fmem.
Qed.

Lemma old_environment_extension_point {G:list form}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)
 R A Next e a output :G ⊢C Op 3 R A A Next ->G ⊢C e ∈' R ->G ⊢C a ∈' A ->
 G ⊢C Ext0 e a output ->G ⊢C output ∈' Next.
Proof.
 intros HOp HE HA HExt. pose proof(CE2 HOp)as H.
 finst H e. fmp H HE. finst H a. fmp H HA. fex H witness HW. fdestr HW HIn HExtW.
 fhave E:(ext0_unique HG HR HOm HC e a witness output HExtW HExt). fmem.
Qed.

Definition old_environment_carrier_zero_law:form:=
 Succ0 $0 $1 →Cl $1 $2 →∃($0 ∈' $3 ∧∀(Emp0 $0 →$0 ∈' $1)).
Definition old_environment_extension_point_law:form:=
 Op 3 $0 $1 $1 $2 →$3 ∈' $0 →$4 ∈' $1 →Ext0 $3 $4 $5 →$5 ∈' $2.

Theorem old_environment_carrier_zero_proof:old_L_background ⊢C old_environment_carrier_zero_law.
Proof.
 unfold old_environment_carrier_zero_law. apply II,II.
 eapply old_environment_carrier_zero with(A:=$0)(S0:=$1)(C:=$2).
 - intros ax H. do 2 right. exact(old_hierarchy_base ax H).
 - do 2 right. exact old_hierarchy_reg.
 - do 2 right. exact old_hierarchy_omega.
 - intros ax H. do 2 right. exact(old_closure_axioms ax H).
 - apply Ctx. right. now left.
 - apply Ctx. now left.
Qed.
Theorem old_environment_extension_point_proof:old_L_background ⊢C old_environment_extension_point_law.
Proof.
 unfold old_environment_extension_point_law. do 4 apply II.
 eapply old_environment_extension_point with(R:=$0)(A:=$1)(Next:=$2)(e:=$3)(a:=$4)(output:=$5).
 - intros ax H. do 4 right. exact(old_hierarchy_base ax H).
 - do 4 right. exact old_hierarchy_reg.
 - do 4 right. exact old_hierarchy_omega.
 - intros ax H. do 4 right. exact(old_closure_axioms ax H).
 - apply Ctx. do 3 right. now left.
 - apply Ctx. do 2 right. now left.
 - apply Ctx. right. now left.
 - apply Ctx. now left.
Qed.

Print Assumptions old_environment_carrier_zero_proof.
Print Assumptions old_environment_extension_point_proof.
