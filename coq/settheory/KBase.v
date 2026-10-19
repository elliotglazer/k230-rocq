(** One finite collection of KP0 instances used by the raw constructions. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KPRaw KPPair KPTransitive.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition KBase : list form := EqAx ++
  [kp0 ⊥; forall_times 1 (kp0 singleton_matrix);
   forall_times 4 (kp0 pair_matrix); kp0 transitive_matrix;
   forall_times 1 (kp0 power_matrix)].

Lemma KBase_ok a : In a KBase -> K0 a.
Proof.
  unfold KBase. intros H. apply in_app_or in H as [H|H].
  - now apply K0_eq.
  - destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (K0_instance ⊥ 0), kp0_closed. exact I.
    + apply K0_instance, kp0_closed. exact singleton_matrix_bounded.
    + apply K0_instance, kp0_closed. exact pair_matrix_bounded.
    + apply (K0_instance transitive_matrix 0), kp0_closed. exact transitive_matrix_bounded.
    + apply K0_instance, kp0_closed. exact power_matrix_bounded.
Qed.

Lemma KBase_eq G : incl KBase G -> incl EqAx G.
Proof. intros H a Ha. apply H. unfold KBase. apply in_or_app. now left. Qed.

Lemma KBase_empty G (HB : incl KBase G) : G ⊢C empty_object.
Proof.
  apply kp0_empty, HB. unfold KBase. apply in_or_app. right. now left.
Qed.

Lemma KBase_singleton G (HB : incl KBase G) a : G ⊢C ∃ raw_singleton a`[↑] $0.
Proof.
  apply kp0_singleton; [now apply KBase_eq|]. apply HB.
  unfold KBase. apply in_or_app. right. cbn. tauto.
Qed.

Lemma KBase_pair G (HB : incl KBase G) a b : G ⊢C ∃ raw_pair a`[↑] b`[↑] $0.
Proof.
  apply kp0_pair; [now apply KBase_eq| | |]; apply HB;
    unfold KBase; apply in_or_app; right; cbn; tauto.
Qed.

Lemma KBase_transitive G (HB : incl KBase G) a :
  G ⊢C ∃ (a`[↑] ∈' $0 ∧ raw_transitive $0).
Proof.
  apply kp0_transitive; [now apply KBase_eq| |]; apply HB;
    unfold KBase; apply in_or_app; right; cbn; tauto.
Qed.

Lemma KBase_power G (HB : incl KBase G) a :
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ raw_subset $0 a`[↑]`[↑]).
Proof.
  apply kp0_power; [now apply KBase_eq|]. apply HB.
  unfold KBase. apply in_or_app. right. cbn. tauto.
Qed.
