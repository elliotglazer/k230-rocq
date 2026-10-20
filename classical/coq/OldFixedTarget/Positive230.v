(** Positive fixed-formula certificates in the original checked library.
    This file uses the original FOL namespace and is compiled separately
    from the current arithmetic-model library. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_tr Std_gen Std_H Std_glue Std_iface
  Std_iface2 Std_setnd Std_setbase L1_LDef L1_LMeta.
From OldK230S Require Import KP0 KPRaw KBase KPrimeTheory KMarkers.
From OldK230L Require Import Codes230 Thm230 Comp_Prop230 CompleteBase230 Complete230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Local Opaque KCode230.P.

Theorem TB_to_positive_formula phi eta :
  TB ⊢TC phi -> oddenv eta -> thm230 (tau (tr eta phi)).
Proof.
  intros [A [HA HP]] Heta.
  pose proof (nd_sound A phi HP eta Heta) as H.
  apply der_foldi in H. apply (Q_discharge _ _ H).
  intros q HQ. apply in_map_iff in HQ as [a [<- Ha]].
  destruct (HA a Ha) as [p [n [Hp [Hn ->]]]].
  exact (Q_tr_cl eta n p Hp Hn).
Qed.

Theorem KPrimeOrd_to_positive_formula phi eta :
  KPrimeOrd ⊢TC phi -> oddenv eta -> thm230 (tau (tr eta phi)).
Proof.
  intros HP HE. apply (TB_to_positive_formula phi eta);[|exact HE].
  exact (theory_derivation_map KPrimeOrd TB phi KPrimeOrd_TB HP).
Qed.

Theorem K0_to_positive_formula phi eta :
  K0 ⊢TC phi -> oddenv eta -> thm230 (tau (tr eta phi)).
Proof.
  intros HP HE. exact (KPrimeOrd_to_positive_formula phi eta
    (K0_derivation_to_KPrimeOrd phi HP) HE).
Qed.

Definition every_marker_has_domain_member : form := ∀ ∃ ($1 ∈' $0).

Theorem K0_proves_every_marker_has_domain_member :
  K0 ⊢TC every_marker_has_domain_member.
Proof.
  exists KBase. split;[exact KBase_ok|].
  assert (HB : incl KBase KBase) by (intros a HA; exact HA).
  unfold every_marker_has_domain_member. fall t.
  match goal with |- ?G ⊢C _ => assert (HB' : incl KBase G) by exact HB end.
  fobtain (KBase_singleton _ HB' t) as x HX.
  fexists x. unfold raw_singleton in HX. exact (CE1 HX).
Qed.

Definition empty_marker_code : nat := wex 4 (wal 2 (wn (wel 2 4))).
Definition every_marker_has_domain_member_code : nat := wal 4 (wex 2 (wel 4 2)).

Lemma empty_marker_code_exact : tau (tr eta0 empty_object) = empty_marker_code.
Proof. reflexivity. Qed.
Lemma domain_member_code_exact :
  tau (tr eta0 every_marker_has_domain_member) = every_marker_has_domain_member_code.
Proof. reflexivity. Qed.

Theorem thm230_empty_marker : thm230 empty_marker_code.
Proof.
  rewrite <- empty_marker_code_exact.
  exact (K0_to_positive_formula empty_object eta0 K0_proves_empty oddenv_eta0).
Qed.

Theorem thm230_every_marker_has_domain_member :
  thm230 every_marker_has_domain_member_code.
Proof.
  rewrite <- domain_member_code_exact.
  exact (K0_to_positive_formula every_marker_has_domain_member eta0
    K0_proves_every_marker_has_domain_member oddenv_eta0).
Qed.

Print Assumptions TB_to_positive_formula.
Print Assumptions K0_to_positive_formula.
Print Assumptions thm230_empty_marker.
Print Assumptions thm230_every_marker_has_domain_member.
