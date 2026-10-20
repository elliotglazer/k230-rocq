(** Concrete finite extensionality certificates in the original verified
    namespace. The marker instance uses free index zero, hence named marker
    1 under eta0. It is not yet alpha-normalized to quotation base 4. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_tr Std_gen Std_iface Std_glue Std_H.
From OldK230S Require Import KP0 KMarkers KQuotFormula KQuotAxioms.
From OldK230L Require Import Codes230 Thm230 Comp_Prop230.
From OldFixedTarget Require Import Positive230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Local Opaque KCode230.P.

Definition marker_extensionality : form := raw_empty $0 → qtrans $0 ax_ext'.
Definition closed_extensionality_code := tau (tr eta0 (qaxiom ax_ext')).
Definition marker_extensionality_code := tau (tr eta0 marker_extensionality).
Definition old_quotient_extensionality_code := tau (tr eta0 (qtrans $0 ax_ext')).

Lemma fixed_extensionality_closed : closedf ax_ext'.
Proof. apply ZF0base_closed. cbn [ZF0base List.In]. tauto. Qed.

Lemma extensionality_marker_instance :
  (raw_empty $0 → qtrans $0 ax_ext'[↑])[$0..] = marker_extensionality.
Proof.
  rewrite (closed_subst ax_ext' ↑ fixed_extensionality_closed).
  cbn [subst_form]. rewrite raw_empty_subst,qtrans_subst.
  rewrite (closed_subst ax_ext' ($0..) fixed_extensionality_closed).
  reflexivity.
Qed.

Theorem K0_proves_marker_extensionality : K0 ⊢TC marker_extensionality.
Proof.
  destruct K0_qext as [A [HA HP]]. exists A. split;[exact HA|].
  unfold qaxiom in HP.
  pose proof (AllE $0 HP) as HI.
  now rewrite extensionality_marker_instance in HI.
Qed.

Theorem thm230_closed_extensionality : thm230 closed_extensionality_code.
Proof.
  exact (K0_to_positive_formula (qaxiom ax_ext') eta0 K0_qext oddenv_eta0).
Qed.

Theorem thm230_marker_extensionality : thm230 marker_extensionality_code.
Proof.
  exact (K0_to_positive_formula marker_extensionality eta0
    K0_proves_marker_extensionality oddenv_eta0).
Qed.

Lemma marker_extensionality_code_exact :
  marker_extensionality_code =
  wim (wal 2 (wn (wel 2 1))) old_quotient_extensionality_code.
Proof. reflexivity. Qed.

Print Assumptions K0_proves_marker_extensionality.
Print Assumptions thm230_closed_extensionality.
Print Assumptions thm230_marker_extensionality.
Print Assumptions marker_extensionality_code_exact.
