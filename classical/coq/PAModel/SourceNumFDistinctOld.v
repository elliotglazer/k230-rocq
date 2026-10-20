(** Fixed irreflexivity facts in both orientations. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_numf_distinct_fact(reverse:bool):form :=
 (if reverse then $1 ∈' $0 else $0 ∈' $1)→$0 ≡' $1 →⊥.
Theorem old_numf_distinct_fact_proof reverse :old_L_background ⊢C old_numf_distinct_fact reverse.
Proof.
 destruct reverse;unfold old_numf_distinct_fact;apply II,II.
 - assert(E:($0 ≡' $1::$1 ∈' $0::old_L_background) ⊢C $0 ≡' $1)by(apply Ctx;now left).
   assert(H:($0 ≡' $1::$1 ∈' $0::old_L_background) ⊢C $1 ∈' $0)by(apply Ctx;right;now left).
   assert(HG:incl ZF0base($0 ≡' $1::$1 ∈' $0::old_L_background))by(intros a HA;do 2 right;exact(old_hierarchy_base a HA)).
   frew_in E ($1`[↑] ∈' $0) H.
   exact(u_no_self HG ltac:(do 2 right;exact old_hierarchy_reg)
     ltac:(do 2 right;exact old_hierarchy_omega)
     ltac:(intros a HA;do 2 right;exact(old_closure_axioms a HA)) $1 H).
 - assert(E:($0 ≡' $1::$0 ∈' $1::old_L_background) ⊢C $0 ≡' $1)by(apply Ctx;now left).
   assert(H:($0 ≡' $1::$0 ∈' $1::old_L_background) ⊢C $0 ∈' $1)by(apply Ctx;right;now left).
   assert(HG:incl ZF0base($0 ≡' $1::$0 ∈' $1::old_L_background))by(intros a HA;do 2 right;exact(old_hierarchy_base a HA)).
   frew_in E ($0 ∈' $1`[↑]) H.
   exact(u_no_self HG ltac:(do 2 right;exact old_hierarchy_reg)
     ltac:(do 2 right;exact old_hierarchy_omega)
     ltac:(intros a HA;do 2 right;exact(old_closure_axioms a HA)) $1 H).
Qed.
Print Assumptions old_numf_distinct_fact_proof.
