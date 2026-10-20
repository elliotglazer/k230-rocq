(** Fixed closure-operation laws needed by the internally uniform numeral
    and definability proofs. There is no varying formula induction here. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma old_closure_axioms :incl Ax_cl old_L_background.
Proof.
  intros a HA. apply old_hierarchy_axioms. unfold Ax_L.
  apply in_app_iff. now left.
Qed.

Definition old_closure_empty_law :form :=Succ0 $0 $1 →Cl $1 $2 →∃(Emp0 $0 ∧$0 ∈' $3).
Definition old_closure_successor_law :form :=Succ0 $0 $1 →Cl $1 $2 →
  ∀($0 ∈' $3 →∃(Succ0 $1 $0 ∧$0 ∈' $4)).

Theorem old_closure_empty_proof :old_L_background ⊢C old_closure_empty_law.
Proof.
  unfold old_closure_empty_law. apply II,II.
  eapply cl_emp with (A:=$0) (S0:=$1) (C:=$2).
  - intros a HA. do 2 right. exact (old_hierarchy_base a HA).
  - do 2 right. exact old_hierarchy_reg.
  - do 2 right. exact old_hierarchy_omega.
  - intros a HA. do 2 right. exact (old_closure_axioms a HA).
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma old_closure_successor_step {G:list form} (HG:incl ZF0base G) (HR:In ax_reg' G)
    (HOm:In ax_om' G) (HC:incl Ax_cl G) A S0 C x :
  G ⊢C Succ0 A S0 ->G ⊢C Cl S0 C ->G ⊢C x ∈' C ->
  G ⊢C ∃(Succ0 x`[↑] $0 ∧$0 ∈' C`[↑]).
Proof.
  intros HS HCl Hx.
  fobtain (cl_op_g HG HR HOm HC 0 S0 C x x x ltac:(lia) HCl Hx Hx Hx) as p Hp.
  fdestr Hp Hp1 Hp2.
  fobtain (cl_op_g HG HR HOm HC 0 S0 C x p p ltac:(lia) HCl Hx Hp1 Hp1) as q Hq.
  fdestr Hq Hq1 Hq2.
  fobtain (cl_op_g HG HR HOm HC 1 S0 C q q q ltac:(lia) HCl Hq1 Hq1 Hq1) as u Hu.
  fdestr Hu Hu1 Hu2.
  fexists u. fsplit;[|exact Hu1]. unfold Succ0. fsplit;[fsplit|].
  - exact (union0_in HG q u p x Hu2 (pair0_r HG x p q Hq2) (pair0_l HG x x p Hp2)).
  - unfold Sub0. fall z. fintro Hz.
    exact (union0_in HG q u x z Hu2 (pair0_l HG x p q Hq2) Hz).
  - fall z. fintro Hz. fhave H : (union0_el HG q u z Hu2 Hz).
    fex H w Hw. fdestr Hw Hw1 Hw2.
    fhave E : (pair0_el HG x p q w Hq2 Hw1). fcases E E1 E2.
    + fleft. fmem.
    + fright. fassert Hzp : (z ∈' p). { fmem. }
      fhave E' : (pair0_el HG x x p z Hp2 Hzp). fcases E' E3 E4;feq.
Qed.

Theorem old_closure_successor_proof :old_L_background ⊢C old_closure_successor_law.
Proof.
  unfold old_closure_successor_law. apply II,II. fall x. apply II.
  eapply old_closure_successor_step with (A:=$0) (S0:=$1) (C:=$2) (x:=x).
  - intros a HA. do 3 right. exact (old_hierarchy_base a HA).
  - do 3 right. exact old_hierarchy_reg.
  - do 3 right. exact old_hierarchy_omega.
  - intros a HA. do 3 right. exact (old_closure_axioms a HA).
  - apply Ctx. do 2 right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Definition old_empty_exists_law :form :=∃ Emp0 $0.
Definition old_successor_exists_law :form :=∃ Succ0 $1 $0.

Theorem old_empty_exists_proof :old_L_background ⊢C old_empty_exists_law.
Proof.
  exact (u_emp0_ex old_hierarchy_base old_hierarchy_reg old_hierarchy_omega old_closure_axioms).
Qed.
Theorem old_successor_exists_proof :old_L_background ⊢C old_successor_exists_law.
Proof.
  exact (u_succ0_ex old_hierarchy_base old_hierarchy_reg old_hierarchy_omega old_closure_axioms $0).
Qed.

Print Assumptions old_closure_empty_proof.
Print Assumptions old_closure_successor_proof.
Print Assumptions old_empty_exists_proof.
Print Assumptions old_successor_exists_proof.
