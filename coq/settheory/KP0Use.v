(** Instantiate a closed KP0 instance at arbitrary parameter terms and seed. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From K230S Require Import KP0.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma kp0_use G n (phi : form) (sg : nat -> term) a :
  In (forall_times n (kp0 phi)) G -> fb (S (S n)) phi ->
  G ⊢C ∃ ((∀ (($0 ≡' a`[↑]`[↑] ∨
                    ∃ ($0 ∈' $2 ∧ ∀ ($0 ∈' $2 → $0 ∈' $1))) →
            ((∃ phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])]) →
             ∃ ($0 ∈' $2 ∧ phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])))) ∧
          ∀ ($0 ∈' $1 → ∃ phi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])])).
Proof.
  intros Hin Hfb.
  assert (H : G ⊢C forall_times n (kp0 phi)) by now apply Ctx.
  apply (closed_inst _ _ _ sg (kp0_closed _ _ Hfb)) in H.
  apply (AllE a) in H. cbn in H.
  replace (phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$0 .: $1 .: (fun k => $(4 + k))][up (up (up (up sg)))][up (up (up a..))])
    by form_subst_eq.
  replace (phi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$1 .: $0 .: (fun k => $(4 + k))][up (up (up (up sg)))][up (up (up a..))])
    by form_subst_eq.
  exact H.
Qed.

(** Equality of explicit substitution expressions, not an extensionality axiom. *)
Ltac ksubst_eq :=
  rewrite ?subst_comp; apply subst_ext;
  intros [|[|[|[|[|[|k]]]]]]; unfold funcomp; cbn;
  autorewrite with fsub; term_eq.
Ltac kform_eq := repeat (first [reflexivity | ksubst_eq | form_subst_eq | progress f_equal]).
Ltac kconv H :=
  match type of H with _ ⊢C ?f => match goal with |- _ ⊢C ?g =>
    replace g with f by kform_eq; exact H end end.
