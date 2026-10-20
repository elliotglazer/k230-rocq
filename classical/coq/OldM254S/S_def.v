(** * S_def: the nonextensional source theory S of the 254-state ZFC machine.

    Signature: the library's minimal one (FOL/Sets/minZF.v), predicates [∈'] and [≡'], no function
    symbols.  [≡'] is first-order equality given by the library's four equality axioms; there is NO
    extensionality, foundation or choice.

      S0 = equality axioms + CP + every closure of a GIC instance
      SIR = S0 + IR   (the PDF's S_IR)

    CP  (container):  ∀p ∃V ( p∈V ∧ ∀x∈V ( x⊆V ∧ ∃W∈V ∀z (z⊆x → z∈W) ) )
    GIC (global-image collection), for a formula [phi] with $0 = input, $1 = output,
         $(k+2) = parameter k:
         ∀B ∃C ( ∀a∈B ∀y (phi(a,y) → ∃y' (phi(a,y') ∧ y'∈C))  ∧  ∀y∈C ∃x phi(x,y) )
    IR  (irreflexivity): ∀x ¬ x∈x

    This is the theory read off the root bundle of zf/m254/inputs/source.py (method [axioms]), with
    the atom Rel(i,j) read as v_i ∈ v_j. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition ax_cp : form :=
  ∀ ∃ ($1 ∈' $0 ∧ ∀ ($0 ∈' $1 →
        (∀ ($0 ∈' $1 → $0 ∈' $2)) ∧
        ∃ ($0 ∈' $2 ∧ ∀ ((∀ ($0 ∈' $1 → $0 ∈' $3)) → $0 ∈' $1)))).

Definition ax_ir : form := ∀ ¬ ($0 ∈' $0).

Definition gic (phi : form) : form :=
  ∀ ∃ ((∀ ($0 ∈' $2 → ∀ (phi[$1 .: $0 .: (fun k => $(4 + k))] →
                         ∃ (phi[$2 .: $0 .: (fun k => $(5 + k))] ∧ $0 ∈' $3))))
       ∧ ∀ ($0 ∈' $1 → ∃ phi[$0 .: $1 .: (fun k => $(4 + k))])).

Definition Sbase : list form := [ax_refl'; ax_sym'; ax_trans'; ax_eq_elem'; ax_cp].

Inductive S0 : form -> Prop :=
  | S0_base phi : In phi Sbase -> S0 phi
  | S0_gic phi n : closedf (forall_times n (gic phi)) -> S0 (forall_times n (gic phi)).

Definition SIR (phi : form) : Prop := S0 phi \/ phi = ax_ir.

Lemma Sbase_closed psi : In psi Sbase -> closedf psi.
Proof. intros H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

Lemma ax_ir_closed : closedf ax_ir.
Proof. cbn. lia. Qed.

Lemma S0_closed psi : S0 psi -> closedf psi.
Proof. intros [phi H | phi n H]; [now apply Sbase_closed | exact H]. Qed.

Lemma SIR_closed psi : SIR psi -> closedf psi.
Proof. intros [H | ->]; [now apply S0_closed | apply ax_ir_closed]. Qed.
