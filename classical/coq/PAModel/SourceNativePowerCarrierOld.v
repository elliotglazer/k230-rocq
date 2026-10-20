(** Genuine fixed Power Set selector argument; no varying K matrix is
 lifted as an externally finite formula. Reflection remains a literal antecedent. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldRegCon Require Import Rel.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL.
From OldK230S Require Import KPRaw KUpperCore.
From PAModel Require Import SourceLFixed SourceLNonempty SourceHierarchyOld SourceRecursionFactsOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
#[local] Arguments Lform:simpl never.
#[local] Arguments InL:simpl never.
#[local] Hint Rewrite Lform_up Lform_inst InL_subst relL_subst relS_subst':fsub.
Ltac native_cp_conv H:=match type of H with _ ⊢C ?f=>match goal with|-_ ⊢C ?g=>
 replace g with f by(repeat(first[reflexivity|form_subst_eq|progress f_equal]));exact H end end.
Definition old_native_cp_zeta:form:=∀((∀($0 ∈' $1 →$0 ∈' $2))→$0 ∈' $2).
Definition old_native_cp_rho:form:=∃(∀((∀($0 ∈' $1 →$0 ∈' $3))→$0 ∈' $1)).
Definition old_native_cp_theta:form:=($2 ∈' $3 ∧old_native_cp_rho)∨((¬($2 ∈' $3))∧old_native_cp_zeta).
Lemma old_native_cp_theta_bound:fb 4 old_native_cp_theta.
Proof. unfold old_native_cp_theta,old_native_cp_rho,old_native_cp_zeta. fbcomp. Qed.
Lemma old_native_reflected_power_container {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HO:In ax_om' G)(HL:incl Ax_L G)
 beta Y s t x:
 incl powL_insts G ->G ⊢C Refl 4 old_native_cp_theta beta ->G ⊢C LL beta Y ->
 G ⊢C s ∈' t ->G ⊢C s ∈' Y ->G ⊢C t ∈' Y ->G ⊢C InL x ->G ⊢C x ∈' Y ->
 G ⊢C ∃($0 ∈' Y`[↑] ∧rel Lform(old_native_cp_zeta[x`[↑] .: $0 .: var])).
Proof.
 intros Hpw HRf HY Hst Hs Ht HxL HxY.
 pose proof(axL_power HG HR HO HL Hpw)as Hpow.
 unfold ax_power' in Hpow. cbn[rel]in Hpow. finst Hpow x. fmp Hpow HxL.
 fex Hpow P HP. fdestr HP HPL HPp. rewrite rel_is_power in HPp.
 fassert Hrho:(rel Lform(old_native_cp_rho[x..])).
 { unfold old_native_cp_rho. simp. fexists P. fsplit;[exact HPL|].
   fall z. fintro HzL. fintro Hsub. finst HPp z. fmp HPp HzL.
   apply(iff_r _ _ _ HPp). rewrite rel_sub'. native_cp_conv Hsub. }
 fassert R1:(rel Lform(old_native_cp_theta[x .: x .: s .: t .: (fun _=>x)])↔
  relS Y(old_native_cp_theta[x .: x .: s .: t .: (fun _=>x)])).
 { eapply(refl_use HG HR HO HL 4 old_native_cp_theta beta Y(x .: x .: s .: t .: (fun _=>x)));
   [exact old_native_cp_theta_bound|exact HRf|exact HY|].
   intros[|[|[|[|i]]]]HI;cbn;[exact HxY|exact HxY|exact Hs|exact Ht|lia]. }
 fassert L1:(rel Lform(old_native_cp_theta[x .: x .: s .: t .: (fun _=>x)])).
 { unfold old_native_cp_theta. simp. fleft. fsplit;[exact Hst|native_cp_conv Hrho]. }
 fhave S1:(iff_l _ _ _ R1 L1). unfold old_native_cp_theta in S1. simp_in S1.
 fcases S1 S1a S1b.
 - fdestr S1a Hunused Hr. unfold old_native_cp_rho in Hr. simp_in Hr.
   fex Hr W HW. fdestr HW HWY HWz.
   fassert R2:(rel Lform(old_native_cp_theta[x .: W .: x .: x .: (fun _=>x)])↔
    relS Y(old_native_cp_theta[x .: W .: x .: x .: (fun _=>x)])).
   { eapply(refl_use HG HR HO HL 4 old_native_cp_theta beta Y(x .: W .: x .: x .: (fun _=>x)));
     [exact old_native_cp_theta_bound|exact HRf|exact HY|].
     intros[|[|[|[|i]]]]HI;cbn;[exact HxY|exact HWY|exact HxY|exact HxY|lia]. }
   fassert S2:(relS Y(old_native_cp_theta[x .: W .: x .: x .: (fun _=>x)])).
   { unfold old_native_cp_theta,old_native_cp_zeta. simp. fright. fsplit.
     - fintro Hxx. exact(no_self_g HG HR x Hxx).
     - native_cp_conv HWz. }
   fhave L2:(iff_r _ _ _ R2 S2). unfold old_native_cp_theta in L2. simp_in L2.
   fcases L2 L2a L2b.
   + fdestr L2a Hxx Hunused2. fabsurd. exact(no_self_g HG HR x Hxx).
   + fdestr L2b Hunused2 Hzeta. fexists W. fsplit;[exact HWY|native_cp_conv Hzeta].
 - fdestr S1b Hnst Hunused. fabsurd. exact(IE Hnst Hst).
Qed.
Lemma old_native_reflected_subset_closed {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HO:In ax_om' G)(HL:incl Ax_L G)
 beta Y s t:
 incl powL_insts G ->G ⊢C Refl 4 old_native_cp_theta beta ->G ⊢C Ord0 beta ->G ⊢C LL beta Y ->
 G ⊢C s ∈' t ->G ⊢C s ∈' Y ->G ⊢C t ∈' Y ->G ⊢C rel Lform(subset_closed Y).
Proof.
 intros Hpw HRf Hbo HY Hst Hs Ht.
 fassert HT:(Trans0 Y). { eapply LL_trans_g;eassumption. }
 unfold subset_closed. simp. fall x. fintro HxL. fintro HxY.
 fall z. fintro HzL. fintro Hsub.
 fobtain(old_native_reflected_power_container HG HR HO HL beta Y s t x Hpw HRf HY Hst Hs Ht HxL HxY)as W HW.
 fdestr HW HWY HWz. unfold old_native_cp_zeta in HWz. simp_in HWz.
 finst HWz z. fmp HWz HzL.
 match type of HWz with _ ⊢C ?A→_=>fassert HS:A end.
 { unfold raw_subset in Hsub. native_cp_conv Hsub. }
 fmp HWz HS. exact(trans0_use Y W z HT HWY HWz).
Qed.
Definition old_native_cp_background:=old_L_background++powL_insts.
Lemma old_native_cp_background_valid q:In q old_native_cp_background ->ZFR q.
Proof.
 intro H. apply in_app_iff in H as[H|H];[exact(old_L_background_valid q H)|].
 exact(oc_insts_ok 0 Qpow q fb_Qpow H).
Qed.
Definition old_native_cp_subset_law:form:=Refl 4 old_native_cp_theta $0 →Ord0 $0 →LL $0 $1 →
 $2 ∈' $3 →$2 ∈' $1 →$3 ∈' $1 →rel Lform(subset_closed $1).
Theorem old_native_cp_subset_proof:old_native_cp_background ⊢C old_native_cp_subset_law.
Proof.
 unfold old_native_cp_subset_law. do 6 apply II. eapply old_native_reflected_subset_closed with(beta:=$0)(Y:=$1)(s:=$2)(t:=$3).
 - intros q HQ. do 6 right. apply in_app_iff. left. exact(old_hierarchy_base q HQ).
 - do 6 right. apply in_app_iff. left. exact old_hierarchy_reg.
 - do 6 right. apply in_app_iff. left. exact old_hierarchy_omega.
 - intros q HQ. do 6 right. apply in_app_iff. left. exact(old_hierarchy_axioms q HQ).
 - intros q HQ. do 6 right. apply in_app_iff. now right.
 - recursion_fixed_context.
 - recursion_fixed_context.
 - recursion_fixed_context.
 - recursion_fixed_context.
 - recursion_fixed_context.
 - recursion_fixed_context.
Qed.
Print Assumptions old_native_reflected_power_container.
Print Assumptions old_native_reflected_subset_closed.
Print Assumptions old_native_cp_subset_proof.
