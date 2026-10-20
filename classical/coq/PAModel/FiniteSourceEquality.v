(** Fixed source equality certificates for the three equality/membership
    rows. Arbitrary internal variable names are handled by proof renaming. *)
From PAModel Require Import SetFormulaCodes FiniteSourceNoSelf.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma finite_set_trans G t u v : In ax_trans' G ->
  G ⊢C t ≡' u -> G ⊢C u ≡' v -> G ⊢C t ≡' v.
Proof.
  intros HT HTU HUV. assert (H:G ⊢C ax_trans') by (apply Ctx;exact HT).
  ns_inst H t. ns_inst H u. ns_inst H v.
  ns_mp H HTU. exact (IE H HUV).
Qed.

Definition finite_equality_axioms : list sf_form := [ax_refl';ax_sym';ax_trans';ax_eq_elem'].
Inductive finite_equality_row := FER3 | FER5 | FER7.
Definition finite_equality_matrix row : sf_form :=
  match row with
  | FER3 => ($0 ≡' $1) → (($2 ∈' $0) → ($2 ∈' $1))
  | FER5 => ($2 ≡' $0) → (($2 ∈' $1) → ($0 ∈' $1))
  | FER7 => ($2 ≡' $0) → (($2 ≡' $1) → ($0 ≡' $1))
  end.

Theorem finite_equality_matrix_derivation row :
  finite_equality_axioms ⊢C finite_equality_matrix row.
Proof.
  assert (HR:In ax_refl' finite_equality_axioms) by (cbn;tauto).
  assert (HS:In ax_sym' finite_equality_axioms) by (cbn;tauto).
  assert (HT:In ax_trans' finite_equality_axioms) by (cbn;tauto).
  assert (HE:In ax_eq_elem' finite_equality_axioms) by (cbn;tauto).
  destruct row;cbn [finite_equality_matrix].
  - ns_intro HEq. ns_intro HM.
    eapply finite_set_mem_cong;[exact HE|apply finite_set_refl;exact HR|exact HEq|exact HM].
  - ns_intro HEq. ns_intro HM.
    eapply finite_set_mem_cong;[exact HE|exact HEq|apply finite_set_refl;exact HR|exact HM].
  - ns_intro HCA. ns_intro HCB.
    eapply finite_set_trans;[exact HT|apply finite_set_sym;[exact HS|exact HCA]|exact HCB].
Qed.

Print Assumptions finite_equality_matrix_derivation.
