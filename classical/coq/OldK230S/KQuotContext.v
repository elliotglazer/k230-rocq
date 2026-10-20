(** A finite source context for quotient logic and Extensionality. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KBase KPSeparation KDomain KCollection KTagged KRelation KQuot KQuotSym KQuotCollect KQuotUnion KQuotExt KQuotFormula.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition KExt : list form := KLogic ++
  [forall_times 3 (kp0 (separation_matrix domain_selector));
   forall_times 6 (kp0 (collection_matrix bisim_forward));
   forall_times 6 (kp0 (collection_matrix bisim_backward));
   forall_times 9 (kp0 (tagged_matrix (relation_selector rooted_union)))].

Lemma KExt_ok a : In a KExt -> K0 a.
Proof.
  unfold KExt. intros H. apply in_app_or in H as [H|[<-|[<-|[<-|[<-|[]]]]]].
  - apply KLogic_ok, H.
  - apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
  - apply K0_instance, kp0_closed, collection_matrix_bounded, bisim_forward_bounded.
  - apply K0_instance, kp0_closed, collection_matrix_bounded, bisim_backward_bounded.
  - apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, rooted_union_bounded.
Qed.

Lemma KExt_logic G : incl KExt G -> incl KLogic G.
Proof. intros H a Ha. apply H. unfold KExt. apply in_or_app. now left. Qed.
Lemma KExt_base G : incl KExt G -> incl KBase G.
Proof. intros H. apply KLogic_base, KExt_logic, H. Qed.
Lemma KExt_envelope G : incl KExt G ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G.
Proof. intros H. apply H. unfold KExt. apply in_or_app; right; cbn; tauto. Qed.
Lemma KExt_forward G : incl KExt G ->
  In (forall_times 6 (kp0 (collection_matrix bisim_forward))) G.
Proof. intros H. apply H. unfold KExt. apply in_or_app; right; cbn; tauto. Qed.
Lemma KExt_backward G : incl KExt G ->
  In (forall_times 6 (kp0 (collection_matrix bisim_backward))) G.
Proof. intros H. apply H. unfold KExt. apply in_or_app; right; cbn; tauto. Qed.
Lemma KExt_union G : incl KExt G ->
  In (forall_times 9 (kp0 (tagged_matrix (relation_selector rooted_union)))) G.
Proof. intros H. apply H. unfold KExt. apply in_or_app; right; cbn; tauto. Qed.

Lemma KExt_ext G (HK : incl KExt G) t x y :
  G ⊢C KMarkers.raw_empty t -> G ⊢C t ∈' x -> G ⊢C t ∈' y ->
  G ⊢C same_dmembers t x y -> G ⊢C deqv t x y.
Proof.
  apply deqv_ext.
  - now apply KExt_base.
  - apply KLogic_diag, KExt_logic, HK.
  - apply KLogic_reverse, KExt_logic, HK.
  - now apply KExt_envelope.
  - now apply KExt_forward.
  - now apply KExt_backward.
  - now apply KExt_union.
Qed.
