(** A fixed finite WF closure derivation in the original minimal calculus.
    Rich-function elimination is applied only to this fixed external proof;
    no internal nonstandard source derivation is passed through it. *)
From OldUndecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts.
From OldUndecidability.FOL.Sets Require Import ZF minZF.
From OldUndecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_minZF PCPb_to_ZFD.
From OldUndecidability.FOL.Sets.Models Require Import ZF_conservativity.
From OldUndecidability Require Import Shared.ListAutomation.
From OldRegCon Require Import Rel WF Main MinZF.
From Stdlib Require Import Lists.List Lia.
Import ListAutomationNotations ListAutomationHints.
Open Scope syn.
Set Implicit Arguments.
#[local] Instance old_wf_fixed_pc : peirce := class.
#[local] Hint Constructors prv : core.
#[local] Instance old_wf_func_dec : eq_dec ZF_func_sig.
Proof. intros x y. unfold dec. decide equality. Defined.
#[local] Instance old_wf_pred_dec : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

Definition old_wf_term := @term sig_empty.
Definition old_wf_form := @form sig_empty ZF_pred_sig _ falsity_on.
Definition old_wf_subset (x y:old_wf_term) : old_wf_form := ∀($0 ∈' x`[↑] → $0 ∈' y`[↑]).
Definition old_wf_transitive (x:old_wf_term) : old_wf_form := ∀($0 ∈' x`[↑] → old_wf_subset $0 x`[↑]).
Definition old_wf_nonempty (s:old_wf_term) : old_wf_form := ∃($0 ∈' s`[↑]).
Definition old_wf_minel (m s:old_wf_term) : old_wf_form := m ∈' s ∧ ∀($0 ∈' m`[↑] → ¬($0 ∈' s`[↑])).
Definition old_wf_minimal (s:old_wf_term) : old_wf_form := ∃ old_wf_minel $0 s`[↑].
Definition old_wf_wellf (t:old_wf_term) : old_wf_form :=
  ∀(old_wf_subset $0 t`[↑] → old_wf_nonempty $0 → old_wf_minimal $0).
Definition old_wf_tw (t:old_wf_term) : old_wf_form := old_wf_transitive t ∧ old_wf_wellf t.
Definition old_wf_class (x:old_wf_term) : old_wf_form := ∃(old_wf_tw $0 ∧ x`[↑] ∈' $0).
Definition old_wf_domain : old_wf_form := old_wf_class $0.
Definition old_wf_closure : old_wf_form := ∀((∀($0 ∈' $1 → old_wf_class $0)) → old_wf_class $0).

Lemma old_wf_class_embed x : embed (old_wf_class x)=WF (embed_t x).
Proof. destruct x as [i|[]]. reflexivity. Qed.

Theorem old_rich_wf_closure : B0 ⊢ embed old_wf_closure.
Proof.
  change (B0 ⊢ ∀((∀($0 ∈ $1 → WF $0)) → WF $0)).
  apply AllI_named. intros x. simp. apply II,WF_closure.
  - intros a HA. right. change (In a (ZFeq' ++ Wax)). apply in_or_app. now left.
  - intros a HA. right. change (In a (ZFeq' ++ Wax)). apply in_or_app. now right.
  - apply Ctx;cbn;tauto.
Qed.

Lemma old_B0_is_core a : In a B0 -> ZFc a.
Proof.
  intro HA. unfold B0 in HA. apply in_app_iff in HA. destruct HA as [HA|HA].
  - now apply ZFc_base.
  - unfold Wax in HA. cbn in HA.
    destruct HA as [<-|[<-|[<-|[<-|[]]]]];unfold CsepT,CsepS,Crep,Csepw.
    + apply (ZFc_sep (phi:=chi $1 $0) (n:=1)).
      apply (proj1 (bounded_comp_eq 1 (ax_sep (chi $1 $0)))). compute;repeat split;lia.
    + apply (ZFc_sep (phi:=$0 ∈ $1) (n:=1)).
      apply (proj1 (bounded_comp_eq 1 (ax_sep ($0 ∈ $1)))). compute;repeat split;lia.
    + apply (ZFc_rep (phi:=canonw $0 $1) (n:=0)).
      apply (proj1 (bounded_comp_eq 0 (ax_rep (canonw $0 $1)))). compute;repeat split;lia.
    + apply (ZFc_sep (phi:=WF $0) (n:=0)).
      apply (proj1 (bounded_comp_eq 0 (ax_sep (WF $0)))). compute;repeat split;lia.
Qed.

Theorem old_minimal_wf_closure :
  exists A:list old_wf_form,(forall a,In a A -> ZFcl_min a) /\ A ⊢ old_wf_closure.
Proof.
  pose proof old_rich_wf_closure as HP.
  assert (HP':(B0 ++ ZFeq') ⊢ embed old_wf_closure) by (apply (Weak HP);auto).
  apply rm_const_prv in HP'.
  destruct (collect (R:=fun L (a:form) => L ⊢ rm_const_fm a) (Q:=ZFcl_min) (A:=B0))
    as [L [HL HPr]].
  - intros A B x HX HAB. exact (Weak HX HAB).
  - intros a HA. now apply rm_const_axiom,old_B0_is_core.
  - exists (L ++ minZFeq'). split.
    + intros a HA. apply in_app_iff in HA. destruct HA as [HA|HA];[now apply HL|now left].
    + apply loop_deductive';[auto|].
      apply (prv_cut HP'). intros a HA. apply in_app_iff in HA.
      destruct HA as [HA|HA].
      * apply in_map_iff in HA. destruct HA as [phi [<- HIn]]. apply (Weak (HPr phi HIn));auto.
      * apply Ctx. apply in_app_iff. now right.
Qed.

Print Assumptions old_rich_wf_closure.
Print Assumptions old_minimal_wf_closure.
