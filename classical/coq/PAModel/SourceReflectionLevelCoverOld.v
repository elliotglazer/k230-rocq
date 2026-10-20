(** Cofinal ordinal levels cover the hierarchy level of their union. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceRecursionFactsOld SourceReflectionUnionOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
Definition old_reflection_level_cover K Lb:form:=
 ∀($0 ∈' Lb`[↑] →∃($0 ∈' K`[↑]`[↑] ∧∃(LL $1 $0 ∧$2 ∈' $0))).
Lemma old_reflection_level_cover_from_union {G}(HG:incl ZF0base G)(HR:In ax_reg' G)(HO:In ax_om' G)(HL:incl Ax_L G)K b Lb:
 G ⊢C old_reflection_ordinals K ->G ⊢C Union0 K b ->G ⊢C Lim0 b ->G ⊢C LL b Lb ->
 G ⊢C old_reflection_level_cover K Lb.
Proof.
 intros HKo HUnion HLim HLL. unfold old_reflection_ordinals in HKo.
 pose proof(LL_lim_g HG HR HO HL b Lb HLim HLL)as T.
 unfold old_reflection_level_cover. fall y. fintro Hy. finst T y. fmp T Hy.
 fex T g Hg. fdestr Hg Hgb Hg2. fex Hg2 Yg HYg. fdestr HYg HYgL HyYg.
 pose proof HUnion as H. unfold Union0 in H. fdestr H H1 H2.
 finst H1 g. fmp H1 Hgb. fex H1 k Hk. fdestr Hk HkK Hgk.
 pose proof HKo as Hko. finst Hko k. fmp Hko HkK.
 fobtain(LL_ex_g HG HR HO HL k Hko)as Xk HXk.
 fhave M:(LL_mono_g HG HR HO HL k g Xk Yg Hko Hgk HXk HYgL). fdestr M M1 M2.
 fexists k. fsplit;[exact HkK|]. fexists Xk. fsplit;[exact HXk|].
 unfold Sub0 in M2. finst M2 y. exact(IE M2 HyYg).
Qed.
Definition old_reflection_level_cover_law:form:=
 old_reflection_ordinals $0 →Union0 $0 $1 →Lim0 $1 →LL $1 $2 →old_reflection_level_cover $0 $2.
Theorem old_reflection_level_cover_proof:old_L_background ⊢C old_reflection_level_cover_law.
Proof.
 unfold old_reflection_level_cover_law. do 4 apply II.
 eapply old_reflection_level_cover_from_union.
 - recursion_fixed_background.
 - do 4 right. exact old_hierarchy_reg.
 - do 4 right. exact old_hierarchy_omega.
 - intros x HX. do 4 right. exact(old_hierarchy_axioms x HX).
 - recursion_fixed_context.
 - recursion_fixed_context.
 - recursion_fixed_context.
 - recursion_fixed_context.
Qed.
Print Assumptions old_reflection_level_cover_from_union.
Print Assumptions old_reflection_level_cover_proof.
