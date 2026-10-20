(** Fixed domain deductions for the actual Ext0 environment operation. *)
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
Local Ltac wk Hinc :=match type of Hinc with incl ?A ?B=>
 repeat match goal with
 | H:A ⊢C _|-_=>apply(fun h=>Weak h Hinc)in H
 | H:incl ?X A|-_=>apply(fun h=>incl_tran h Hinc)in H
 | H:In ?x A|-_=>apply Hinc in H
 end end.
Lemma old_env_domain_empty {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)e d:
 G ⊢C Emp0 e ->G ⊢C Emp0 d ->G ⊢C Dom0 e d.
Proof.
 intros He Hd. apply(dom0_intro HG HR HOm HC).
 - intros G' u HGG' Hu. wk HGG'. fabsurd. exact(emp0_el HG d u Hd Hu).
 - intros G' u v HGG' Huv. wk HGG'. unfold App0 in Huv. fex Huv p Hp. fdestr Hp Hp1 Hp2.
   fabsurd. exact(emp0_el HG e p He Hp1).
Qed.
Lemma old_env_domain_extension {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)e d s v z:
 G ⊢C Dom0 e d ->G ⊢C Succ0 d s ->G ⊢C Ext0 e v z ->G ⊢C Dom0 z s.
Proof.
 intros Hdom Hd2 He2. fobtain(u_op0_ex HG HR HOm HC d v)as p Hp.
 fhave Ha:(ext0_char HG HR HOm HC e v z d p He2 Hdom Hp).
 apply(dom0_intro HG HR HOm HC).
 - intros G' u HGG' Hu. wk HGG'. fhave E:(succ0_el HG d s u Hd2 Hu). fcases E E1 E2.
   + fobtain(u_dom0_app HG HR HOm HC e d u Hdom E1)as w Hw. fexists w.
     exact(iff_r _ _ _(app_adj HG HR HOm HC e p z u w Ha)(DI1 _ Hw)).
   + fexists v. apply(iff_r _ _ _(app_adj HG HR HOm HC e p z u v Ha)). fright.
     frew E2(OP0 $0 v`[↑] p`[↑]). exact Hp.
 - intros G' u w HGG' Huv. wk HGG'. fhave H:(iff_l _ _ _(app_adj HG HR HOm HC e p z u w Ha)Huv).
   fcases H H1 H2.
   + exact(sub0_use HG d s u(succ0_sub HG d s Hd2)(u_dom0_in HG HR HOm HC e d u w Hdom H1)).
   + fhave E:(CE1(u_op0_inj HG HR HOm HC u w d v p H2 Hp)).
     fhave H3:(succ0_self HG d s Hd2). fmem.
Qed.
Definition old_env_domain_empty_law:form:=Emp0 $0 →Emp0 $1 →Dom0 $0 $1.
Definition old_env_domain_extension_law:form:=Dom0 $0 $1 →Succ0 $1 $2 →Ext0 $0 $3 $4 →Dom0 $4 $2.
Ltac env_domain_bg :=intros f Hf;repeat first[solve[exact(old_hierarchy_base f Hf)]|right].
Ltac env_domain_cl :=intros f Hf;repeat first[solve[exact(old_closure_axioms f Hf)]|right].
Ltac env_domain_reg :=repeat first[solve[exact old_hierarchy_reg]|right].
Ltac env_domain_omega :=repeat first[solve[exact old_hierarchy_omega]|right].
Ltac env_domain_ctx :=apply Ctx;cbn;tauto.
Theorem old_env_domain_empty_proof:old_L_background ⊢C old_env_domain_empty_law.
Proof.
 unfold old_env_domain_empty_law. apply II,II. eapply old_env_domain_empty;
 [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx].
Qed.
Theorem old_env_domain_extension_proof:old_L_background ⊢C old_env_domain_extension_law.
Proof.
 unfold old_env_domain_extension_law. apply II,II,II. eapply old_env_domain_extension;
 [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_env_domain_empty_proof.
Print Assumptions old_env_domain_extension_proof.
