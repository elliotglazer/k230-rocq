(** A singleton of an empty set witnesses nonemptiness of the WF domain.
    Only the fixed equality, Empty and Pair axioms are used. *)
From PAModel Require Import SetFormulaCodes SourceWFFormula.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Undecidability Require Import Shared.ListAutomation.
From Stdlib Require Import Lists.List.
Import ListAutomationNotations ListAutomationHints.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance wf_empty_pc : peirce := class.
#[local] Hint Constructors prv : core.

Definition wf_empty (x:sf_term) : sf_form := ∀ ¬($0 ∈' x`[↑]).
Definition wf_empty_children (t:sf_term) : sf_form := ∀($0 ∈' t`[↑] → wf_empty $0).
Arguments wf_empty : simpl never.
Arguments wf_empty_children : simpl never.
Lemma wf_empty_subst x sigma : (wf_empty x)[sigma]=wf_empty x`[sigma].
Proof. unfold wf_empty. cbn. now rewrite up_term. Qed.
Lemma wf_empty_children_subst x sigma :
  (wf_empty_children x)[sigma]=wf_empty_children x`[sigma].
Proof. unfold wf_empty_children. cbn. rewrite wf_empty_subst. cbn. now rewrite up_term. Qed.
#[export] Hint Rewrite wf_empty_subst wf_empty_children_subst : wf_source_subst.

Lemma wf_source_empty_elim T x y phi :
  T ⊢ wf_empty x -> T ⊢ y ∈' x -> T ⊢ phi.
Proof.
  intros HE HY. apply Exp. unfold wf_empty in HE. apply (AllE y) in HE. wf_simp_in HE.
  eapply IE;[exact HE|exact HY].
Qed.
Lemma wf_source_empty_children_elim T t x :
  T ⊢ wf_empty_children t -> T ⊢ x ∈' t -> T ⊢ wf_empty x.
Proof.
  intros HE HX. unfold wf_empty_children in HE. apply (AllE x) in HE. wf_simp_in HE.
  eapply IE;[exact HE|exact HX].
Qed.

Theorem wf_source_empty_children_tw T t : T ⊢ wf_empty_children t -> T ⊢ wf_tw t.
Proof.
  intro HE. unfold wf_tw. apply CI.
  - unfold wf_transitive. apply AllI_named. intros x. wf_simp. apply II.
    apply wf_source_subset_intro. intros y.
    eapply wf_source_empty_elim with (x:=x) (y:=y).
    + eapply wf_source_empty_children_elim with (t:=t).
      * apply (Weak HE). auto.
      * apply Ctx;cbn;tauto.
    + apply Ctx;cbn;tauto.
  - unfold wf_wellf. apply AllI_named. intros s. wf_simp. apply II,II.
    assert (HN:(wf_nonempty s :: wf_subset s t :: T) ⊢ wf_nonempty s) by (apply Ctx;cbn;tauto).
    unfold wf_nonempty in HN. apply (ExE_named HN). intros w. wf_simp.
    unfold wf_minimal. apply (ExI w). wf_simp. unfold wf_minel. apply CI.
    + apply Ctx;cbn;tauto.
    + apply AllI_named. intros z. wf_simp. apply II,II.
      eapply wf_source_empty_elim with (x:=w) (y:=z).
      * eapply wf_source_empty_children_elim with (t:=t).
        -- apply (Weak HE). intros a Ha;cbn;tauto.
        -- eapply wf_source_subset_elim with (x:=s) (y:=t).
           ++ apply Ctx;cbn;tauto.
           ++ apply Ctx;cbn;tauto.
      * apply Ctx;cbn;tauto.
Qed.

Lemma wf_source_refl T x : In ax_refl' T -> T ⊢ x ≡' x.
Proof.
  intro H. assert (HP:T ⊢ ax_refl') by (apply Ctx,H).
  unfold ax_refl' in HP. apply (AllE x) in HP. wf_simp_in HP. exact HP.
Qed.

Lemma wf_source_member_congruence T x y x' y' :
  In ax_eq_elem' T -> T ⊢ x ≡' x' -> T ⊢ y ≡' y' -> T ⊢ x ∈' y -> T ⊢ x' ∈' y'.
Proof.
  intros HA HX HY HM. assert (HP:T ⊢ ax_eq_elem') by (apply Ctx,HA).
  unfold ax_eq_elem' in HP.
  apply (AllE x),(AllE y),(AllE x'),(AllE y') in HP. wf_simp_in HP.
  eapply IE;[eapply IE;[eapply IE;[exact HP|exact HX]|exact HY]|exact HM].
Qed.

Lemma wf_source_pair_empty_children T e t :
  In ax_refl' T -> In ax_eq_elem' T -> T ⊢ wf_empty e -> T ⊢ is_pair e e t ->
  T ⊢ wf_empty_children t.
Proof.
  intros HRef HEq HEmpty HPair. unfold wf_empty_children.
  apply AllI_named. intros x. wf_simp. apply II.
  assert (HP:(x ∈' t :: T) ⊢ is_pair e e t) by (apply (Weak HPair);auto).
  unfold is_pair in HP. apply (AllE x) in HP. wf_simp_in HP.
  assert (HX:(x ∈' t :: T) ⊢ x ≡' e).
  { assert (HD:(x ∈' t :: T) ⊢ x ≡' e ∨ x ≡' e).
    { eapply IE;[eapply CE1;exact HP|apply Ctx;cbn;tauto]. }
    eapply DE;[exact HD|apply Ctx;cbn;tauto|apply Ctx;cbn;tauto]. }
  unfold wf_empty. apply AllI_named. intros z. wf_simp. apply II.
  eapply wf_source_empty_elim with (x:=e) (y:=z).
  - apply (Weak HEmpty). intros a Ha;cbn;tauto.
  - eapply wf_source_member_congruence with (x:=z) (y:=x).
    + cbn. auto.
    + apply wf_source_refl. cbn;auto.
    + apply (Weak HX). intros a Ha;cbn;tauto.
    + apply Ctx;cbn;tauto.
Qed.

Lemma wf_source_pair_has_empty T e t :
  In ax_refl' T -> T ⊢ is_pair e e t -> T ⊢ e ∈' t.
Proof.
  intros HR HP. unfold is_pair in HP. apply (AllE e) in HP. wf_simp_in HP.
  eapply IE;[eapply CE2;exact HP|]. apply DI1,wf_source_refl,HR.
Qed.

Theorem wf_domain_nonempty_prv : minZFeq' ⊢ ∃ wf_domain.
Proof.
  assert (HE:minZFeq' ⊢ ax_eset') by (apply Ctx;unfold minZFeq',minZF';cbn;tauto).
  unfold ax_eset' in HE. apply (ExE_named HE). intros e. wf_simp.
  assert (HP:(is_eset e :: minZFeq') ⊢ ax_pair') by
    (apply Ctx;unfold minZFeq',minZF';cbn;tauto).
  unfold ax_pair' in HP. apply (AllE e),(AllE e) in HP. wf_simp_in HP.
  apply (ExE_named HP). intros t. wf_simp.
  apply (ExI e). wf_simp. apply wf_source_class_intro with t.
  - apply wf_source_empty_children_tw.
    apply wf_source_pair_empty_children with e.
    + unfold minZFeq';cbn;tauto.
    + unfold minZFeq';cbn;tauto.
    + change ((is_pair e e t :: is_eset e :: minZFeq') ⊢ is_eset e).
      apply Ctx;cbn;tauto.
    + apply Ctx;cbn;tauto.
  - apply wf_source_pair_has_empty.
    + unfold minZFeq';cbn;tauto.
    + apply Ctx;cbn;tauto.
Qed.

Print Assumptions wf_source_empty_children_tw.
Print Assumptions wf_domain_nonempty_prv.


