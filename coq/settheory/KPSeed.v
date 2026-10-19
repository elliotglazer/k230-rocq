(** Direct logical conversion of an output-root schema to its seed form.
    The classical case split is an object-level ND derivation. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0Use.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** P has an output at index 0; H has a container at index 0.
    All other indices in the two formulas are common parameters. *)
Definition output_root (P H : form) : form :=
  ∀ ∃ ((P[↑] → $1 ∈' $0) ∧ H[up ↑]).

Definition seed_root (P H : form) : form :=
  ∃ (((∃ P)[↑] → ∃ ($0 ∈' $1 ∧ P[up ↑])) ∧ H).

Lemma lifted_shift_cancel (P : form) t : P[up ↑][up t..] = P.
Proof. rewrite subst_comp. apply subst_id. intros [|n]; reflexivity. Qed.

Theorem output_root_to_seed G P H :
  G ⊢C output_root P H -> G ⊢C seed_root P H.
Proof.
  intros Hsource. apply (XM_rule G (∃ P)).
  - fintro Hsome. fex Hsome x Hx.
    unfold output_root in Hsource. finst Hsource x.
    fex Hsource c Hc. fdestr Hc Hroot Hclosure.
    unfold seed_root. fexists c. fsplit.
    + fintro Hsome. fexists x. fsplit.
      * apply (IE Hroot). kconv Hx.
      * kconv Hx.
    + kconv Hclosure.
  - fintro Hnone. unfold output_root in Hsource. finst Hsource ($0).
    fex Hsource c Hc. fdestr Hc Hroot Hclosure.
    unfold seed_root. fexists c. fsplit.
    + fintro Hsome. fabsurd. apply (IE Hnone).
      rewrite lifted_shift_cancel in Hsome. exact Hsome.
    + kconv Hclosure.
Qed.
