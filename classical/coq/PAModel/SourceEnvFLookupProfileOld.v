(** Fixed lookup-profile deductions, with the value quantifier discharged. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceEnvFDomainOld SourceEnvFLookupOld SourceAtomLookupOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.

Lemma old_env_lookup_head_profile {G}(HG:incl ZF0base G)(HR:In ax_reg' G)
 (HOm:In ax_om' G)(HC:incl Ax_cl G)e d a z i:
 G ⊢C Dom0 e d ->G ⊢C Ext0 e a z ->G ⊢C i ≡' d ->G ⊢C old_atom_app_profile z i a.
Proof.
 intros HD HE HI. unfold old_atom_app_profile. fall w.
 eapply old_env_lookup_head; eassumption.
Qed.
Lemma old_env_lookup_tail_profile {G}(HG:incl ZF0base G)(HR:In ax_reg' G)
 (HOm:In ax_om' G)(HC:incl Ax_cl G)e d a z i b:
 G ⊢C Dom0 e d ->G ⊢C Ext0 e a z ->G ⊢C(i ≡' d→⊥) ->
 G ⊢C old_atom_app_profile e i b ->G ⊢C old_atom_app_profile z i b.
Proof.
 intros HD HE HI HP. unfold old_atom_app_profile. fall w.
 fhave H1:(old_env_lookup_tail HG HR HOm HC e d a z i w HD HE HI).
 fhave H2:(old_atom_app_profile_use e i b w HP). fsplit.
 - fintro H. exact(iff_l _ _ _ H2(iff_l _ _ _ H1 H)).
 - fintro H. exact(iff_r _ _ _ H1(iff_r _ _ _ H2 H)).
Qed.
Definition old_env_lookup_profile_law(head:bool):form:=Dom0 $0 $1 →Ext0 $0 $2 $3 →
 (if head then $4 ≡' $1 else($4 ≡' $1→⊥)) →
 (if head then old_atom_app_profile $3 $4 $2 else
  old_atom_app_profile $0 $4 $5 →old_atom_app_profile $3 $4 $5).
Theorem old_env_lookup_profile_proof head:old_L_background ⊢C old_env_lookup_profile_law head.
Proof.
 destruct head;unfold old_env_lookup_profile_law.
 - apply II,II,II. eapply old_env_lookup_head_profile;
   [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx|env_domain_ctx].
 - apply II,II,II,II. eapply old_env_lookup_tail_profile;
   [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_env_lookup_head_profile.
Print Assumptions old_env_lookup_tail_profile.
Print Assumptions old_env_lookup_profile_proof.
