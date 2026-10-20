(** The finite step of reflection's cofinal common-level argument. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord Z_L Z_refl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceRecursionFactsOld
  SourceReflectionUnionOld SourceReflectionLevelCoverOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.

Definition old_cofinal_extension(K k X y:term):form:=∃(∃
  ((($1 ∈' K`[↑]`[↑] ∧Ord0 $1) ∧LL $1 $0) ∧
    (Sub0 X`[↑]`[↑] $0 ∧y`[↑]`[↑] ∈' $0))).

Lemma old_cofinal_level_extension {G}(HG:incl ZF0base G)(HR:In ax_reg' G)
    (HO:In ax_om' G)(HL:incl Ax_L G)K Lb k X y:
  G ⊢C old_reflection_ordinals K ->G ⊢C old_reflection_level_cover K Lb ->
  G ⊢C k ∈' K ->G ⊢C LL k X ->G ⊢C y ∈' Lb ->
  G ⊢C old_cofinal_extension K k X y.
Proof.
  intros HKo HCover Hk HX Hy.
  unfold old_reflection_ordinals in HKo. unfold old_reflection_level_cover in HCover.
  finst HCover y. fmp HCover Hy. fex HCover w Hw. fdestr Hw HwK HW.
  fex HW Y HY. fdestr HY HYL HyY.
  pose proof HKo as Hko. finst Hko k. fmp Hko Hk.
  pose proof HKo as Hwo. finst Hwo w. fmp Hwo HwK.
  fhave T:(rw_ord_tri HG HR HO HL k w Hko Hwo). fcases T T1 T3. fcases T1 Ta Tb.
  - fhave M:(LL_mono_g HG HR HO HL w k Y X Hwo Ta HYL HX). fdestr M MX MSub.
    unfold old_cofinal_extension. fexists w. fexists Y. fsplit.
    + fsplit;[fsplit;assumption|exact HYL].
    + fsplit;assumption.
  - frew_in Tb(LL $0 Y`[↑])HYL.
    fhave E:(LL_unique_g HG HR HO HL k Y X Hko HYL HX).
    unfold old_cofinal_extension. fexists k. fexists X. fsplit.
    + fsplit;[fsplit;assumption|exact HX].
    + fsplit;[exact(sub_refl0 X)|]. fmem.
  - fhave M:(LL_mono_g HG HR HO HL k w X Y Hko T3 HX HYL). fdestr M MX MSub.
    unfold old_cofinal_extension. fexists k. fexists X. fsplit.
    + fsplit;[fsplit;assumption|exact HX].
    + fsplit;[exact(sub_refl0 X)|]. unfold Sub0 in MSub. finst MSub y. exact(IE MSub HyY).
Qed.

Definition old_cofinal_extension_law:form:=
  old_reflection_ordinals $0 →old_reflection_level_cover $0 $1 →
  $2 ∈' $0 →LL $2 $3 →$4 ∈' $1 →old_cofinal_extension $0 $2 $3 $4.
Theorem old_cofinal_extension_proof:old_L_background ⊢C old_cofinal_extension_law.
Proof.
  unfold old_cofinal_extension_law. do 5 apply II.
  eapply old_cofinal_level_extension.
  - recursion_fixed_background.
  - do 5 right. exact old_hierarchy_reg.
  - do 5 right. exact old_hierarchy_omega.
  - intros z Hz. do 5 right. exact(old_hierarchy_axioms z Hz).
  - recursion_fixed_context.
  - recursion_fixed_context.
  - recursion_fixed_context.
  - recursion_fixed_context.
  - recursion_fixed_context.
Qed.
Print Assumptions old_cofinal_level_extension.
Print Assumptions old_cofinal_extension_proof.
