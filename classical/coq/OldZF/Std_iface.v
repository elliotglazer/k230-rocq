(** * Std_iface: the target theory and the set-theoretic interface.

    [ZFc] = the library's minZFeq axioms (FOL/Sets/minZF.v) with the separation and replacement
    instances universally closed (the axiom set of the library's own semantic entailment, which
    requires axioms to hold under every assignment).  [ZF0] = [ZFc] without the infinity axiom.

    [INF_lib] = O'Rear's (Zermelo-style) infinity axiom in library syntax:
      forall x, exists y, x in y /\ forall u, u in y -> exists z, z in y /\ forall w, (w in z <-> w = u).

    Set-theoretic obligations (ND derivations, closed hypotheses only):
      [Inf_ZF_to_OR] : ZF0 + ax_om'  ⊢ INF_lib
      [Inf_OR_to_ZF] : ZF0 + INF_lib ⊢ ax_om'                                                *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

(** closed formulas (no free de Bruijn index), with the simple predicate [fb] of Std_tr *)
Definition closedf (phi : form) : Prop := fb 0 phi.

Definition ZF0base : list form :=
  [ax_refl'; ax_sym'; ax_trans'; ax_eq_elem'; ax_ext'; ax_eset'; ax_pair'; ax_union'; ax_power'].

Inductive ZF0 : form -> Prop :=
  | ZF0_base phi : In phi ZF0base -> ZF0 phi
  | ZF0_sep phi n : closedf (forall_times n (ax_sep' phi)) -> ZF0 (forall_times n (ax_sep' phi))
  | ZF0_rep phi n : closedf (forall_times n (ax_rep' phi)) -> ZF0 (forall_times n (ax_rep' phi)).

Definition ZFc (phi : form) : Prop := ZF0 phi \/ phi = ax_om'.

Definition INF_lib : form :=
  ∀ ∃ ($1 ∈' $0 ∧ ∀ ($0 ∈' $1 → ∃ ($0 ∈' $2 ∧ ∀ (($0 ∈' $1 → $0 ≡' $2) ∧ ($0 ≡' $2 → $0 ∈' $1))))).

(** derivability from a theory, classical *)
Definition thm (T : form -> Prop) (phi : form) : Prop :=
  exists A, (forall psi, In psi A -> T psi) /\ A ⊢C phi.

Definition Inf_ZF_to_OR : Prop := thm (fun psi => ZF0 psi \/ psi = ax_om') INF_lib.
Definition Inf_OR_to_ZF : Prop := thm (fun psi => ZF0 psi \/ psi = INF_lib) ax_om'.

(** helper facts about closed formulas *)
From OldZF Require Import Std_gen.

Lemma closed_subst (phi : form) (sg : nat -> term) : closedf phi -> phi[sg] = phi.
Proof. intro H. rewrite (subst_ext_fb _ 0 sg var H) by (intros; lia). apply subst_var. Qed.

Lemma closed_map_shift (A : list form) : (forall psi, In psi A -> closedf psi) -> map (subst_form ↑) A = A.
Proof.
  induction A as [|a A IH]; intros H; [reflexivity|]. cbn. rewrite closed_subst by (apply H; now left).
  f_equal. apply IH. intros; apply H; now right.
Qed.

(** with closed hypotheses, universal generalization is unrestricted *)
Lemma AllI_closed (A : list form) (phi : form) : (forall psi, In psi A -> closedf psi) -> A ⊢C phi -> A ⊢C ∀ phi.
Proof. intros HA H. apply AllI. now rewrite closed_map_shift. Qed.

Lemma ZF0base_closed psi : In psi ZF0base -> closedf psi.
Proof. intros H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

Lemma INF_lib_closed : closedf INF_lib.
Proof. cbn. lia. Qed.

Lemma ax_om'_closed : closedf ax_om'.
Proof. cbn. lia. Qed.
