(** The factored KP0 theory in the reference's first-order syntax.

    This is the ordinary fresh-variable core from kp0_interpretation.md.
    It is not yet the full decoded theory searched by the literal machine.
    In [phi], index 0 is output, index 1 is input, and indices 2+k are
    parameters. Every occurrence below explicitly supplies that environment.

    Object-level equality is the predicate [equal] with the four displayed
    equality axioms. No set extensionality, foundation or choice is included.
    The Coq inductive below describes the axiom set; it adds no Coq axiom. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition kp0 (phi : form) : form :=
  ∀ ∃ ((∀ (($0 ≡' $2 ∨
                  ∃ ($0 ∈' $2 ∧ ∀ ($0 ∈' $2 → $0 ∈' $1))) →
          ((∃ phi[$0 .: $1 .: (fun k => $(4 + k))]) →
           ∃ ($0 ∈' $2 ∧ phi[$0 .: $1 .: (fun k => $(4 + k))])))) ∧
        ∀ ($0 ∈' $1 → ∃ phi[$1 .: $0 .: (fun k => $(4 + k))])).

Definition equality_axioms : list form :=
  [ax_refl'; ax_sym'; ax_trans'; ax_eq_elem'].

Inductive K0 : form -> Prop :=
  | K0_eq phi : In phi equality_axioms -> K0 phi
  | K0_instance phi n : closedf (forall_times n (kp0 phi)) ->
      K0 (forall_times n (kp0 phi)).

Definition irreflexivity : form := ∀ ¬ ($0 ∈' $0).
Definition K0IR (phi : form) : Prop := K0 phi \/ phi = irreflexivity.

Lemma kp0_closed n (phi : form) : fb (S (S n)) phi ->
  closedf (forall_times n (kp0 phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv.
  rewrite Nat.add_0_r. unfold kp0. cbn.
  repeat split; try lia;
    (eapply fb_subst; [exact H|]); intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma K0_closed phi : K0 phi -> closedf phi.
Proof.
  intros [psi H | psi n H]; [|exact H].
  repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H.
Qed.

Definition empty_object : form := ∃ ∀ ($0 ∈' $1 → ⊥).

(** One false-matrix instance suffices, with an explicit ND derivation. *)
Lemma kp0_empty G : In (kp0 ⊥) G -> G ⊢C empty_object.
Proof.
  intros Hin. assert (H : G ⊢C kp0 ⊥) by now apply Ctx.
  unfold kp0 in H. finst H ($0).
  fex H C HC. fdestr HC Hrequest Hsupport.
  unfold empty_object. fexists C. fall z. fintro Hz.
  finst Hsupport z. fmp Hsupport Hz. fex Hsupport p Hp.
  exact Hp.
Qed.

Theorem K0_proves_empty : K0 ⊢TC empty_object.
Proof.
  exists [kp0 ⊥]. split.
  - intros a [<-|[]]. apply (K0_instance ⊥ 0), kp0_closed. exact I.
  - apply kp0_empty. now left.
Qed.
