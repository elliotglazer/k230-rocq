(** Fixed head/tail lookup deductions for the actual Ext0 operation. *)
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
Lemma old_env_lookup_head {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)e d a z x w:
 G ⊢C Dom0 e d ->G ⊢C Ext0 e a z ->G ⊢C x ≡' d ->G ⊢C App0 z x w ↔w ≡' a.
Proof.
 intros Hdom Hext E. fobtain(u_op0_ex HG HR HOm HC d a)as p Hp.
 fhave Ha:(ext0_char HG HR HOm HC e a z d p Hext Hdom Hp).
 fhave Hiff:(app_adj HG HR HOm HC e p z x w Ha). fsplit.
 - fintro H. fhave H':(iff_l _ _ _ Hiff H). fcases H' H1 H2.
   + fhave Hxd:(u_dom0_in HG HR HOm HC e d x w Hdom H1).
     fabsurd. apply(u_no_self HG HR HOm HC d). fmem.
   + exact(CE2(u_op0_inj HG HR HOm HC x w d a p H2 Hp)).
 - fintro H. apply(iff_r _ _ _ Hiff). fright.
   frew E(OP0 $0 w`[↑] p`[↑]). frew H(OP0 d`[↑] $0 p`[↑]). exact Hp.
Qed.
Lemma old_env_lookup_tail {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)e d a z x w:
 G ⊢C Dom0 e d ->G ⊢C Ext0 e a z ->G ⊢C(x ≡' d→⊥) ->G ⊢C App0 z x w ↔App0 e x w.
Proof.
 intros Hdom Hext Hneq. fobtain(u_op0_ex HG HR HOm HC d a)as p Hp.
 fhave Ha:(ext0_char HG HR HOm HC e a z d p Hext Hdom Hp).
 fhave Hiff:(app_adj HG HR HOm HC e p z x w Ha). fsplit.
 - fintro H. fhave H':(iff_l _ _ _ Hiff H). fcases H' H1 H2.
   + exact H1.
   + fabsurd. exact(IE Hneq(CE1(u_op0_inj HG HR HOm HC x w d a p H2 Hp))).
 - fintro H. apply(iff_r _ _ _ Hiff). fleft. exact H.
Qed.
Definition old_env_lookup_law(head:bool):form:=Dom0 $0 $1 →Ext0 $0 $2 $3 →
 (if head then $4 ≡' $1 else($4 ≡' $1→⊥))→
 (App0 $3 $4 $5 ↔(if head then $5 ≡' $2 else App0 $0 $4 $5)).
Theorem old_env_lookup_proof head:old_L_background ⊢C old_env_lookup_law head.
Proof.
 destruct head;unfold old_env_lookup_law;apply II,II,II.
 - eapply old_env_lookup_head;[env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx|env_domain_ctx].
 - eapply old_env_lookup_tail;[env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_env_lookup_proof.
