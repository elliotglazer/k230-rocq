(** Fixed pair and union witnesses in the shared representative frame. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceEnvFDomainOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Definition old_named_pair_certificate:form:=Succ0 $1 $7 →Cl $7 $2 →$3 ∈' $2 →$4 ∈' $2 →
 ∃($0 ∈' $3 ∧Pair0 $4 $5 $0).
Definition old_named_union_certificate:form:=Succ0 $1 $7 →Cl $7 $2 →$3 ∈' $2 →$5 ∈' $2 →
 ∃($0 ∈' $3 ∧Union0 $6 $0).
Theorem old_named_pair_proof:old_L_background ⊢C old_named_pair_certificate.
Proof.
 unfold old_named_pair_certificate. do 4 apply II.
 eapply cl_op_g with(k:=0)(B:=$7)(C:=$2)(a:=$3)(b:=$4)(c:=$4);
 [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|lia|
  env_domain_ctx|env_domain_ctx|env_domain_ctx|env_domain_ctx].
Qed.
Theorem old_named_union_proof:old_L_background ⊢C old_named_union_certificate.
Proof.
 unfold old_named_union_certificate. do 4 apply II.
 eapply cl_op_g with(k:=1)(B:=$7)(C:=$2)(a:=$5)(b:=$5)(c:=$5);
 [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|lia|
  env_domain_ctx|env_domain_ctx|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_named_pair_proof.
Print Assumptions old_named_union_proof.
