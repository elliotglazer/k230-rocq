(** Fixed total-successor and set-induction use laws for phSig. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setinf Std_setrec.
From PAModel Require Import SourceLFixed.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_recursion_induction_law(induction:bool):form:=if induction then
 (SInd phSig $0 $1 →$0 ∈' $2 →
  (∀($0 ∈' $3 →∃(Rel2 phSig $1 $0 ∧$0 ∈' $4))) →∀($0 ∈' $2 →$0 ∈' $3))
 else(STot phSig $0 →$1 ∈' $0 →∃(Rel2 phSig $2 $0 ∧$0 ∈' $1)).
Theorem old_recursion_induction_proof induction:old_L_background ⊢C old_recursion_induction_law induction.
Proof.
 destruct induction;unfold old_recursion_induction_law.
 - apply II,II,II. apply(sind_use phSig $0 $1 $2);apply Ctx;cbn;tauto.
 - apply II,II. apply(stot_use phSig $0 $1);apply Ctx;cbn;tauto.
Qed.
Print Assumptions old_recursion_induction_proof.
