(** Fixed Op4 existence in the distinct An4/child3/C2 witness frame. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld SourceEnvFDomainOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Definition old_projection_named_law:form:=Succ0 $1 $7 →Cl $7 $2 →$4 ∈' $2 →$3 ∈' $2 →
 ∃($0 ∈' $3 ∧Op 4 $5 $4 $2 $0).
Theorem old_projection_named_proof:old_L_background ⊢C old_projection_named_law.
Proof.
 unfold old_projection_named_law. apply II,II,II,II.
 eapply cl_op_g with(k:=4)(B:=$7)(C:=$2)(a:=$4)(b:=$3)(c:=$1).
 - env_domain_bg.
 - env_domain_reg.
 - env_domain_omega.
 - env_domain_cl.
 - lia.
 - env_domain_ctx.
 - env_domain_ctx.
 - env_domain_ctx.
 - eapply clA_in with(A:=$1)(S0:=$7)(C:=$2);
   [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_projection_named_proof.
