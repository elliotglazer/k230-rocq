(** Lift the checked bound-to-container deduction to a definable class. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From RegCon Require Import Rel.
From K230S Require Import KP0Use KPrimeCore KUpperCore.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition upper_conclusion (phi : form) (sg : nat -> term) (a x : term) : form :=
  ∃ ((phi[x`[↑] .: a`[↑] .: (fun k => (sg k)`[↑])] → x`[↑] ∈' $0) ∧
    (emitted_closure phi)[$0 .: a`[↑] .: (fun k => (sg k)`[↑])]).

Lemma subset_closed_subst b rho : (subset_closed b)[rho] = subset_closed b`[rho].
Proof. psubst subset_closed. Qed.

Lemma witness_closed_subst phi sg b rho :
  (witness_closed phi sg b)[rho] =
  witness_closed phi (fun k => (sg k)`[rho]) b`[rho].
Proof.
  unfold witness_closed, matrix_request.
  repeat progress (cbn; autorewrite with fsub). kform_eq.
Qed.

Lemma upper_conclusion_subst phi sg a x rho :
  (upper_conclusion phi sg a x)[rho] =
  upper_conclusion phi (fun k => (sg k)`[rho]) a`[rho] x`[rho].
Proof.
  unfold upper_conclusion, emitted_closure.
  repeat progress (cbn; autorewrite with fsub). kform_eq.
Qed.

#[global] Hint Rewrite subset_closed_subst witness_closed_subst upper_conclusion_subst : fsub.

Lemma bounded_output_root_rel G m phi sg b a x M (HM : bounded 1 M) rho :
  fb (S (S m)) phi ->
  (forall k, G ⊢C M[(rho k)..]) ->
  G ⊢C (rel M (forall_times (S m) (ax_sep' (trace_predicate phi))))[rho] ->
  G ⊢C (rel M (a ∈' b))[rho] ->
  G ⊢C (rel M (x ∈' b))[rho] ->
  G ⊢C (rel M (subset_closed b))[rho] ->
  G ⊢C (rel M (witness_closed phi sg b))[rho] ->
  G ⊢C (rel M (upper_conclusion phi sg a x))[rho].
Proof.
  intros Hfb HD Hsep Hab Hxb HS HW.
  set (si := forall_times (S m) (ax_sep' (trace_predicate phi))).
  set (A := [si; a ∈' b; x ∈' b; subset_closed b; witness_closed phi sg b]).
  assert (D : A ⊢C upper_conclusion phi sg a x).
  { unfold upper_conclusion. apply (bounded_output_root A m phi sg b a x Hfb).
    - unfold A. now left.
    - apply Ctx. unfold A. right. now left.
    - apply Ctx. unfold A. right. right. now left.
    - apply Ctx. unfold A. right. right. right. now left.
    - apply Ctx. unfold A. right. right. right. right. now left. }
  refine (@rel_prv _ _ M HM class nil _ _ A _ D G rho _ HD _).
  - intros q tau [].
  - intros Gamma f v. destruct f.
  - intros q [].
  - intros q Hq. unfold A in Hq.
    destruct Hq as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption.
Qed.

Lemma bounded_output_root_rel_terms G m phi sg b a x M (HM : bounded 1 M) :
  fb (S (S m)) phi ->
  G ⊢C M[b..] -> G ⊢C M[a..] -> G ⊢C M[x..] ->
  (forall k, G ⊢C M[(sg k)..]) ->
  G ⊢C rel M (forall_times (S m) (ax_sep' (trace_predicate phi))) ->
  G ⊢C a ∈' b -> G ⊢C x ∈' b ->
  G ⊢C rel M (subset_closed b) -> G ⊢C rel M (witness_closed phi sg b) ->
  G ⊢C rel M (upper_conclusion phi sg a x).
Proof.
  intros Hfb Hb Ha Hx Hsg Hsep Hab Hxb HS HW.
  set (rho := b .: a .: x .: sg).
  assert (HD : forall k, G ⊢C M[(rho k)..]).
  { intros [|[|[|k]]]; cbn; assumption || apply Hsg. }
  assert (Hc : closedf (forall_times (S m) (ax_sep' (trace_predicate phi)))).
  { apply sep_closed, trace_predicate_bounded, Hfb. }
  pose proof (bounded_output_root_rel G m phi (fun k => $(3+k)) $0 $1 $2 M HM rho Hfb HD) as H.
  rewrite (rel_subst HM), (closed_subst _ rho Hc) in H.
  specialize (H Hsep).
  cbn [rel] in H.
  assert (Ha' : G ⊢C ($1 ∈' $0)[rho]) by exact Hab.
  assert (Hx' : G ⊢C ($2 ∈' $0)[rho]) by exact Hxb.
  specialize (H Ha' Hx').
  rewrite (rel_subst HM), subset_closed_subst in H.
  specialize (H HS).
  rewrite (rel_subst HM), witness_closed_subst in H.
  specialize (H HW).
  rewrite (rel_subst HM), upper_conclusion_subst in H.
  exact H.
Qed.
