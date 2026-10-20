(** Import-isolated original proof, transferred to the current pure
    arithmetic code calculus by induction on its thm230 derivation. *)
From OldFixedTarget Require Extensionality230.
From OldK230L Require Thm230 Codes230.
From K230L Require Thm230 Codes230.
From Coq Require Import Arith Lia.
Unset Implicit Arguments.

From PAModel Require Import ThmConstructorBridge.

Theorem current_closed_extensionality_certificate :
  K230L.Thm230.thm230 OldFixedTarget.Extensionality230.closed_extensionality_code.
Proof.
  apply original_thm230_to_current.
  exact OldFixedTarget.Extensionality230.thm230_closed_extensionality.
Qed.

Theorem current_marker_extensionality_certificate :
  K230L.Thm230.thm230 OldFixedTarget.Extensionality230.marker_extensionality_code.
Proof.
  apply original_thm230_to_current.
  exact OldFixedTarget.Extensionality230.thm230_marker_extensionality.
Qed.

Theorem current_marker_extensionality_code_exact :
  OldFixedTarget.Extensionality230.marker_extensionality_code =
  K230S.KCode230.wim (K230S.KCode230.wal 2 (K230S.KCode230.wn (K230S.KCode230.wel 2 1)))
    OldFixedTarget.Extensionality230.old_quotient_extensionality_code.
Proof. exact OldFixedTarget.Extensionality230.marker_extensionality_code_exact. Qed.

Print Assumptions original_thm230_to_current.
Print Assumptions current_closed_extensionality_certificate.
Print Assumptions current_marker_extensionality_certificate.
Print Assumptions current_marker_extensionality_code_exact.
