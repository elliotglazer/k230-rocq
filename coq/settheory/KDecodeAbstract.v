(** Abstraction of an arbitrary named matrix into two ordinary active roles.
    This direction does not restrict the matrix to a translation image and
    therefore applies to every decoded natural number. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_dB Std_alpha Std_F Std_tr Std_brnd.
From K230S Require Import KPRaw KDecodeBundle.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition abstract_env (a b v : nat) : term :=
  if Nat.eqb v b then $0 else if Nat.eqb v a then $1 else $(v+2).
Definition abstract_matrix a b q : form := dB (abstract_env a b) q.
Definition decode_env a b k (rho : nat -> term) x y C :=
  upd (upd (upd rho a y) b x) k C.

Lemma abstract_matrix_inst a b q rho x y :
  (abstract_matrix a b q)[x .: y .: rho] = dB (upd (upd rho a y) b x) q.
Proof.
  unfold abstract_matrix. rewrite dB_subst. apply dB_ext. intros v.
  unfold abstract_env, upd, funcomp.
  destruct (Nat.eqb v b), (Nat.eqb v a); cbn; try reflexivity.
  replace (v+2) with (S (S v)) by lia. reflexivity.
Qed.

Lemma decode_env_matrix a b k rho x y C q : fr k q = false ->
  dB (decode_env a b k rho x y C) q = (abstract_matrix a b q)[x .: y .: rho].
Proof.
  intros Hfresh. rewrite abstract_matrix_inst. apply dB_ext_fr. intros v Hv.
  unfold decode_env, upd. destruct (Nat.eqb_spec v k) as [->|Hne];
    [congruence|reflexivity].
Qed.

Lemma decode_env_root a b k rho C q :
  dB (upd rho k C) q = dB (decode_env a b k rho (rho b) (rho a) C) q.
Proof.
  apply dB_ext. intros v. unfold decode_env, upd.
  repeat match goal with
  | |- context [Nat.eqb ?u ?w] => destruct (Nat.eqb_spec u w)
  end; subst; reflexivity.
Qed.

Lemma decode_env_output a b k rho x y C z q : k <> b ->
  dB (upd (decode_env a b k rho x y C) b z) q =
  dB (decode_env a b k rho z y C) q.
Proof.
  intros Hkb. apply dB_ext. intros v. unfold decode_env, upd.
  repeat match goal with
  | |- context [Nat.eqb ?u ?w] => destruct (Nat.eqb_spec u w)
  end; subst; try reflexivity; congruence.
Qed.

Lemma decode_env_input a b k rho x y C z q : a <> b -> k <> a ->
  dB (upd (decode_env a b k rho x y C) a z) q =
  dB (decode_env a b k rho x z C) q.
Proof.
  intros Hab Hka. apply dB_ext. intros v. unfold decode_env, upd.
  repeat match goal with
  | |- context [Nat.eqb ?u ?w] => destruct (Nat.eqb_spec u w)
  end; subst; try reflexivity; congruence.
Qed.

Lemma decode_env_output_value a b k rho x y C : k <> b ->
  decode_env a b k rho x y C b = x.
Proof.
  intros Hkb. unfold decode_env. rewrite upd_neq by congruence. apply upd_eq.
Qed.

Lemma decode_env_input_value a b k rho x y C : a <> b -> k <> a ->
  decode_env a b k rho x y C a = y.
Proof.
  intros Hab Hka. unfold decode_env. rewrite !upd_neq by congruence. apply upd_eq.
Qed.

Lemma decode_env_container_value a b k rho x y C :
  decode_env a b k rho x y C k = C.
Proof. apply upd_eq. Qed.

Lemma decode_env_member a b k rho x y C : k <> b ->
  dB (decode_env a b k rho x y C) (Wel b k) = x ∈' C.
Proof.
  intros Hkb. cbn [dB]. rewrite decode_env_output_value by exact Hkb.
  rewrite decode_env_container_value. reflexivity.
Qed.

Lemma decode_env_subset a b k rho x y C : a <> b -> k <> a -> k <> b ->
  dB (decode_env a b k rho x y C) (KSubset a b k) = raw_subset y x.
Proof.
  intros Hab Hka Hkb. unfold KSubset, raw_subset. cbn [dB].
  rewrite shift_env_eq. rewrite !shift_env_neq by congruence.
  rewrite decode_env_input_value, decode_env_output_value by assumption.
  reflexivity.
Qed.
