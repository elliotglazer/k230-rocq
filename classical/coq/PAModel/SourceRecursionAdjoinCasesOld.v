(** Fixed set-theoretic value cases for adjoining one ordered pair. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setrec.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_recursion_adjoin_cases_law:form:=Adj $0 $1 $2 →OP $3 $4 $1 →App $2 $5 $6 →
 (App $0 $5 $6 ∨($5 ≡' $3 ∧$6 ≡' $4)).
Ltac rec_cases_background:=intros z Hz;repeat first[solve[exact(old_hierarchy_base z Hz)]|right].
Ltac rec_cases_context:=apply Ctx;cbn;tauto.
Theorem old_recursion_adjoin_cases_proof:old_L_background ⊢C old_recursion_adjoin_cases_law.
Proof.
 unfold old_recursion_adjoin_cases_law. apply II,II,II.
 set(ctx:=App $2 $5 $6::OP $3 $4 $1::Adj $0 $1 $2::old_L_background).
 assert(HG:incl ZF0base ctx)by rec_cases_background.
 assert(HA:ctx ⊢C Adj $0 $1 $2)by rec_cases_context.
 assert(HOP:ctx ⊢C OP $3 $4 $1)by rec_cases_context.
 assert(HApp:ctx ⊢C App $2 $5 $6)by rec_cases_context.
 unfold ctx in *.
 pose proof(app_adj_el HG $0 $1 $2 $5 $6 HA HApp)as Cases.
 fcases Cases C1 C2.
 - apply DI1. exact C1.
 - apply DI2. exact(op_inj HG $5 $6 $3 $4 $1 $1 C2 HOP(eq_refl' HG $1)).
Qed.
Print Assumptions old_recursion_adjoin_cases_proof.
