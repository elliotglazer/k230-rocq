(** The ten fixed minZFeq' axioms, using the original K0 quotient proofs. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_tr Std_gen Std_iface Std_glue Std_H.
From OldK230S Require Import KP0 KMarkers KQuotFormula KQuotAxioms KQuotZFTransfer.
From OldK230L Require Import Codes230 Thm230 Comp_Prop230.
From OldFixedTarget Require Import Positive230 Extensionality230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Local Opaque KCode230.P.

Inductive core_fixed_tag :=
| CoreRefl | CoreSym | CoreTrans | CoreEqElem | CoreExt
| CoreEmpty | CorePair | CoreUnion | CorePower | CoreOmega.

Definition core_fixed_source tag : form :=
  match tag with
  | CoreRefl => ax_refl' | CoreSym => ax_sym' | CoreTrans => ax_trans'
  | CoreEqElem => ax_eq_elem' | CoreExt => ax_ext' | CoreEmpty => ax_eset'
  | CorePair => ax_pair' | CoreUnion => ax_union' | CorePower => ax_power'
  | CoreOmega => ax_om'
  end.

Lemma core_fixed_closed tag : closedf (core_fixed_source tag).
Proof.
  destruct tag; cbn [core_fixed_source];
    first [apply ax_om'_closed | apply ZF0base_closed; cbn [ZF0base List.In];tauto].
Qed.

Theorem K0_core_fixed_quotient tag : K0 ⊢TC qaxiom (core_fixed_source tag).
Proof.
  destruct tag;cbn [core_fixed_source].
  - exact K0_qrefl.
  - exact K0_qsym.
  - exact K0_qtrans.
  - exact K0_qeq_elem.
  - exact K0_qext.
  - exact K0_qeset.
  - exact K0_qpair.
  - exact K0_qunion.
  - exact K0_qpower.
  - exact K0_qomega.
Qed.

Definition core_marker_formula tag := raw_empty $0 → qtrans $0 (core_fixed_source tag).
Definition core_marker_code tag := tau (tr eta0 (core_marker_formula tag)).
Definition core_quotient_code tag := tau (tr eta0 (qtrans $0 (core_fixed_source tag))).

Lemma core_marker_instance tag :
  (raw_empty $0 → qtrans $0 (core_fixed_source tag)[↑])[$0..] = core_marker_formula tag.
Proof.
  rewrite (closed_subst _ ↑ (core_fixed_closed tag)).
  cbn [subst_form]. rewrite raw_empty_subst,qtrans_subst.
  rewrite (closed_subst _ ($0..) (core_fixed_closed tag)). reflexivity.
Qed.

Theorem K0_core_marker tag : K0 ⊢TC core_marker_formula tag.
Proof.
  destruct (K0_core_fixed_quotient tag) as [A [HA HP]].
  exists A. split;[exact HA|]. unfold qaxiom in HP.
  pose proof (AllE $0 HP) as HI. now rewrite core_marker_instance in HI.
Qed.

Theorem original_core_marker_certificate tag : thm230 (core_marker_code tag).
Proof.
  destruct tag.
  5: exact thm230_marker_extensionality.
  all: apply (K0_to_positive_formula _ eta0);[apply K0_core_marker|exact oddenv_eta0].
Qed.

Lemma core_marker_code_shape tag :
  core_marker_code tag = wim (wal 2 (wn (wel 2 1))) (core_quotient_code tag).
Proof. destruct tag;reflexivity. Qed.

Print Assumptions core_fixed_closed.
Print Assumptions K0_core_fixed_quotient.
Print Assumptions K0_core_marker.
Print Assumptions original_core_marker_certificate.
Print Assumptions core_marker_code_shape.
