(** The fixed carrier-membership law from the literal closure definition. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceEnvFDomainOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Definition old_closure_carrier_law:form:=Succ0 $0 $1 →Cl $1 $2 →$0 ∈' $2.
Theorem old_closure_carrier_proof:old_L_background ⊢C old_closure_carrier_law.
Proof.
 unfold old_closure_carrier_law. apply II,II. eapply clA_in with(A:=$0)(S0:=$1)(C:=$2);
 [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_closure_carrier_proof.
