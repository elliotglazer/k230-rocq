(** A constructive supply of genuine numerical instances.
    The encoder follows Comp_Prop254.tau, without importing thm254.
    Excluding the atom Wel 0 0 gives a literal round trip; interpreting the
    unrestricted relative-falsity cases remains a separate obligation. *)
From Coq Require Import Arith Lia.
From OldZF Require Import Logic Std_alpha.
From OldK230S Require Import KCode230 KDecoder230 KDecodeFresh KDecodeBundle.

Fixpoint encode230 (p : wff) : nat :=
  match p with
  | Weq x y => weq x y
  | Wel x y => wel x y
  | Wim p q => wim (encode230 p) (encode230 q)
  | Wn p => wn (encode230 p)
  | Wal x p => wal x (encode230 p)
  end.

Fixpoint no_relative_atom (p : wff) : Prop :=
  match p with
  | Weq _ _ => True
  | Wel x y => (x,y) <> (0,0)
  | Wim p q => no_relative_atom p /\ no_relative_atom q
  | Wn p | Wal _ p => no_relative_atom p
  end.

Lemma encode230_positive p : 0 < encode230 p.
Proof.
  induction p as [x y|x y|p IHp q IHq|p IH|x p IH]; cbn [encode230].
  - unfold weq. lia.
  - unfold wel. lia.
  - unfold wim. pose proof (P_ge_r (encode230 p) (encode230 q)). lia.
  - unfold wn, wim, F. pose proof (P_ge_r (encode230 p) 1). lia.
  - unfold wal. lia.
Qed.

Lemma encode230_eq_one p : encode230 p = 1 -> p = Wel 0 0.
Proof.
  destruct p as [x y|x y|p q|p|x p]; cbn [encode230].
  - unfold weq. lia.
  - unfold wel. intros H. assert (P x y = 0) by lia.
    apply P_0 in H0 as [-> ->]. reflexivity.
  - unfold wim. lia.
  - unfold wn, wim. lia.
  - unfold wal. lia.
Qed.

Lemma safe_encode230_ne_one p : no_relative_atom p -> encode230 p <> 1.
Proof.
  intros H E. apply encode230_eq_one in E. subst p. exact (H eq_refl).
Qed.

Theorem D_encode230 p : no_relative_atom p -> D (encode230 p) = p.
Proof.
  induction p as [x y|x y|p IHp q IHq|p IH|x p IH];
    cbn [encode230 no_relative_atom]; intros H.
  - apply D_weq.
  - apply D_wel.
  - destruct H as [Hp Hq]. rewrite D_wim.
    + now rewrite IHp, IHq.
    + now apply safe_encode230_ne_one.
    + apply pair_nonzero_r. pose proof (encode230_positive q). lia.
  - rewrite D_wn. now rewrite IH.
  - rewrite D_wal. now rewrite IH.
Qed.

Theorem encode230_private_fresh p : no_relative_atom p ->
  fr (encode230 p) p = false.
Proof.
  intros H. pose proof (D_private_fresh (encode230 p)) as Hfresh.
  now rewrite (@D_encode230 p H) in Hfresh.
Qed.

Definition padded230 (p : wff) : nat := encode230 (Wn (Wn p)).

Lemma padded230_gt_three p : 3 < padded230 p.
Proof.
  unfold padded230. cbn [encode230]. unfold wn, wim, F.
  pose proof (P_ge_r (4 * P (encode230 p) 1) 1). lia.
Qed.

Theorem D_padded230 p : no_relative_atom p ->
  D (padded230 p) = Wn (Wn p).
Proof. intros H. apply D_encode230. exact H. Qed.

Theorem enabled_padded230_instance p : no_relative_atom p ->
  D (gated230 1 3 (padded230 p)) =
  KBundle 1 3 (padded230 p) (Wn (Wn p)).
Proof.
  intros H. rewrite D_gated230_enabled.
  - now rewrite D_padded230.
  - pose proof (padded230_gt_three p). lia.
  - pose proof (padded230_gt_three p). lia.
Qed.
