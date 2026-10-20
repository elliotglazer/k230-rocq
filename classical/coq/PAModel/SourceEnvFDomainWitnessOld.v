(** Finite role instances of the proved Dom0 construction laws. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld SourceEnvFDomainOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_env_domain_witness_empty_law:form:=Emp0 $1 →Emp0 $0 →Dom0 $1 $0.
Definition old_env_domain_witness_extension_law:form:=Dom0 $1 $0 →Succ0 $0 $2 →Ext0 $1 $4 $3 →Dom0 $3 $2.
Local Ltac ew_bg :=intros f Hf;repeat first[solve[exact(old_hierarchy_base f Hf)]|right].
Local Ltac ew_cl :=intros f Hf;repeat first[solve[exact(old_closure_axioms f Hf)]|right].
Local Ltac ew_reg :=repeat first[solve[exact old_hierarchy_reg]|right].
Local Ltac ew_omega :=repeat first[solve[exact old_hierarchy_omega]|right].
Local Ltac ew_ctx :=apply Ctx;cbn;tauto.
Theorem old_env_domain_witness_empty_proof:old_L_background ⊢C old_env_domain_witness_empty_law.
Proof.
 unfold old_env_domain_witness_empty_law. apply II,II. eapply old_env_domain_empty;
 [ew_bg|ew_reg|ew_omega|ew_cl|ew_ctx|ew_ctx].
Qed.
Theorem old_env_domain_witness_extension_proof:old_L_background ⊢C old_env_domain_witness_extension_law.
Proof.
 unfold old_env_domain_witness_extension_law. apply II,II,II. eapply old_env_domain_extension;
 [ew_bg|ew_reg|ew_omega|ew_cl|ew_ctx|ew_ctx|ew_ctx].
Qed.
Print Assumptions old_env_domain_witness_empty_proof.
Print Assumptions old_env_domain_witness_extension_proof.
