(** Actual finite seed base. A seed in K is deliberately required: a
    cofinal cover of an empty carrier alone need not make K inhabited. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceRecursionFactsOld SourceReflectionUnionOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
Definition old_cofinal_common_empty K:form:=
 ∃∃($1∈K`[↑]`[↑] ∧((Ord0 $1 ∧LL $1 $0) ∧(⊥→⊥))).
Definition old_cofinal_common_seed_law:form:=
 $1∈$0 →old_reflection_ordinals $0 →old_cofinal_common_empty $0.
Lemma old_cofinal_common_seed_g {G}(HG:incl ZF0base G)(HR:In ax_reg' G)
 (HO:In ax_om' G)(HL:incl Ax_L G)K seed:
 G ⊢C seed∈K ->G ⊢C old_reflection_ordinals K ->G ⊢C old_cofinal_common_empty K.
Proof.
 intros HSeed HOrd. unfold old_reflection_ordinals in HOrd. finst HOrd seed. fmp HOrd HSeed.
 fobtain(LL_ex_g HG HR HO HL seed HOrd)as Y HY.
 unfold old_cofinal_common_empty. fexists seed. fexists Y. fsplit.
 - exact HSeed.
 - fsplit.
   + fsplit.
     * exact HOrd.
     * exact HY.
   + apply II,Ctx. now left.
Qed.
Theorem old_cofinal_common_seed_proof:old_L_background ⊢C old_cofinal_common_seed_law.
Proof.
 unfold old_cofinal_common_seed_law. do 2 apply II.
 eapply old_cofinal_common_seed_g.
 - recursion_fixed_background.
 - do 2 right. exact old_hierarchy_reg.
 - do 2 right. exact old_hierarchy_omega.
 - intros f HF. do 2 right. exact(old_hierarchy_axioms f HF).
 - recursion_fixed_context.
 - recursion_fixed_context.
Qed.
Print Assumptions old_cofinal_common_seed_proof.
