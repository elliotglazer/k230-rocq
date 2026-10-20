(** Environments for the frozen active labels a=1, b=3.  The private
    container may numerically coincide with an unused parameter name;
    freshness of the formula, rather than an extra parameter bound, removes
    that update. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_dB Std_tr Std_alpha Std_F Std_iface
  Std_setnd Std_setbase Std_breq Std_brnd.
From OldK230S Require Import KP0Use KPRaw KDecodeBundle KDecodeTranslate KDecodeBridge.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition source_env (sg : nat -> term) (x a : term) (v : nat) : term :=
  if Nat.eqb v 3 then x else if Nat.eqb v 1 then a
  else sg (Nat.div2 (v - 5)).

Definition private_env sg x a c C := upd (source_env sg x a) c C.

Lemma source_env_names sg x a n :
  source_env sg x a (source_names n) = (x .: a .: sg) n.
Proof.
  destruct n as [|[|n]]; cbn [source_names]; try reflexivity.
  unfold source_env.
  destruct (Nat.eqb_spec (2*n+5) 3); [lia|].
  destruct (Nat.eqb_spec (2*n+5) 1); [lia|].
  replace (2*n+5-5) with (2*n) by lia. now rewrite Nat.div2_double.
Qed.

Lemma private_env_output sg x a c C y q : 3 < c ->
  dB (upd (private_env sg x a c C) 3 y) q =
  dB (private_env sg y a c C) q.
Proof.
  intros Hc. apply dB_ext. intros v. unfold private_env, source_env, upd.
  repeat match goal with
  | |- context [Nat.eqb ?u ?w] => destruct (Nat.eqb_spec u w)
  end; subst; try reflexivity; lia.
Qed.

Lemma private_env_input sg x a c C b q : 3 < c ->
  dB (upd (private_env sg x a c C) 1 b) q =
  dB (private_env sg x b c C) q.
Proof.
  intros Hc. apply dB_ext. intros v. unfold private_env, source_env, upd.
  repeat match goal with
  | |- context [Nat.eqb ?u ?w] => destruct (Nat.eqb_spec u w)
  end; subst; try reflexivity; lia.
Qed.

Lemma private_env_fresh sg x a c C q : fr c q = false ->
  dB (private_env sg x a c C) q = dB (source_env sg x a) q.
Proof.
  intros Hfresh. apply dB_ext_fr. intros v Hv. unfold private_env, upd.
  destruct (Nat.eqb_spec v c) as [->|Hne]; [congruence|reflexivity].
Qed.

Lemma private_env_output_value sg x a c C : 3 < c ->
  private_env sg x a c C 3 = x.
Proof. intros Hc. unfold private_env. rewrite upd_neq by lia. reflexivity. Qed.

Lemma private_env_input_value sg x a c C : 3 < c ->
  private_env sg x a c C 1 = a.
Proof. intros Hc. unfold private_env. rewrite upd_neq by lia. reflexivity. Qed.

Lemma private_env_container_value sg x a c C :
  private_env sg x a c C c = C.
Proof. apply upd_eq. Qed.

Theorem private_env_matrix G (phi : form) N sg x a c C :
  incl EqAx G -> fb N phi -> fr c (tr source_names phi) = false ->
  G ⊢C dB (private_env sg x a c C) (tr source_names phi) ↔ phi[x .: a .: sg].
Proof.
  intros HE Hfb Hfresh. rewrite private_env_fresh by exact Hfresh.
  replace (phi[x .: a .: sg]) with
    (phi[fun n => source_env sg x a (source_names n)]).
  - apply (ordinary_matrix230_equiv G phi N); assumption.
  - apply subst_ext. exact (source_env_names sg x a).
Qed.

Lemma private_env_subset sg x a c C : 3 < c ->
  dB (private_env sg x a c C) (KSubset 1 3 c) = raw_subset a x.
Proof.
  intros Hc. unfold KSubset, raw_subset. cbn [dB].
  rewrite shift_env_eq. rewrite !shift_env_neq by lia.
  rewrite private_env_input_value, private_env_output_value by exact Hc.
  reflexivity.
Qed.

Lemma private_env_member sg x a c C : 3 < c ->
  dB (private_env sg x a c C) (Wel 3 c) = x ∈' C.
Proof.
  intros Hc. cbn [dB].
  rewrite private_env_output_value by exact Hc.
  rewrite private_env_container_value. reflexivity.
Qed.
