(** Fixed ordinal-union geometry in the pinned full reflection argument. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceRecursionFactsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
Definition old_reflection_ordinals K:form:=∀($0 ∈' K`[↑] →Ord0 $0).
Definition old_reflection_no_last K:form:=∀($0 ∈' K`[↑] →∃($0 ∈' K`[↑]`[↑] ∧$1 ∈' $0)).
Definition old_reflection_union_subsets K b:form:=∀($0 ∈' K`[↑] →Sub0 $0 b`[↑]).
Definition old_reflection_union_result K b a:form:=Ord0 b ∧(Lim0 b ∧(a ∈' b ∧old_reflection_union_subsets K b)).
Lemma old_reflection_union_geometry {G}(HG:incl ZF0base G)K b a:
 G ⊢C a ∈' K ->G ⊢C old_reflection_ordinals K ->G ⊢C old_reflection_no_last K ->G ⊢C Union0 K b ->
 G ⊢C old_reflection_union_result K b a.
Proof.
 intros Ha HKo HNext HUnion. unfold old_reflection_ordinals in HKo. unfold old_reflection_no_last in HNext.
 fassert HSub:(∀($0 ∈' K`[↑] →Sub0 $0 b`[↑])).
 { fall k. fintro Hk. unfold Sub0. fall z. fintro Hz.
   pose proof HUnion as H. unfold Union0 in H. fdestr H H1 H2.
   finst H2 k. fmp H2 Hk. finst H2 z. exact(IE H2 Hz). }
 fassert Hbo:(Ord0 b). { exact(ord_union_g HG K b HKo HUnion). }
 fassert Hab:(a ∈' b).
 { pose proof HNext as H. finst H a. fmp H Ha. fex H w Hw. fdestr Hw HwK Haw.
   pose proof HSub as H2. finst H2 w. fmp H2 HwK. unfold Sub0 in H2. finst H2 a. exact(IE H2 Haw). }
 fassert Hlim:(Lim0 b).
 { unfold Lim0. fsplit;[fsplit|].
   - exact Hbo.
   - fexists a. fsplit;[exact Hab|feq].
   - fall x. fintro Hx. pose proof HUnion as H. unfold Union0 in H. fdestr H H1 H2.
     finst H1 x. fmp H1 Hx. fex H1 k Hk. fdestr Hk HkK Hxk.
     pose proof HNext as HN. finst HN k. fmp HN HkK. fex HN w Hw. fdestr Hw HwK Hkw.
     fexists k. fsplit;[|exact Hxk]. pose proof HSub as HS. finst HS w. fmp HS HwK.
     unfold Sub0 in HS. finst HS k. exact(IE HS Hkw). }
 unfold old_reflection_union_result,old_reflection_union_subsets.
 fsplit;[exact Hbo|]. fsplit;[exact Hlim|]. fsplit;[exact Hab|exact HSub].
Qed.
Definition old_reflection_union_law:form:=
 $2 ∈' $0 →old_reflection_ordinals $0 →old_reflection_no_last $0 →Union0 $0 $1 →
 old_reflection_union_result $0 $1 $2.
Theorem old_reflection_union_proof:old_L_background ⊢C old_reflection_union_law.
Proof.
 unfold old_reflection_union_law. do 4 apply II.
 eapply old_reflection_union_geometry;
 [recursion_fixed_background|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context].
Qed.
Print Assumptions old_reflection_union_geometry.
Print Assumptions old_reflection_union_proof.
