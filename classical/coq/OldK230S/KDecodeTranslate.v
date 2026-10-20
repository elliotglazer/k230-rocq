(** Ordinary formulas have concrete enabled source codes.  This file uses the
    pinned Std_tr translation; it does not identify a decoded KCore with the
    de Bruijn KPrimeOrd instance or assert source-program completeness. *)
From Coq Require Import Arith Lia.
From OldUndecidability.FOL Require Import Sets.minZF.
From OldZF Require Import Logic L1_LMeta Std_tr Std_alpha.
From OldK230S Require Import KCode230 KDecoder230 KDecodeFresh KDecodeBundle
  KDecodeEncode KDecodeLogic.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Theorem tr_no_relative_atom {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta :
  (forall n, 0 < eta n) -> no_relative_atom (tr eta phi).
Proof.
  revert eta. induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa];
    intros eta Heta.
  - cbn [tr botw no_relative_atom]. exact I.
  - destruct P; cbn [tr no_relative_atom]; try exact I.
    intros H. pose proof (f_equal fst H) as E.
    cbn in E. rewrite tv_idx in E.
    pose proof (Heta (idx (Vector.hd v))). lia.
  - pose proof (IHa eta Heta) as Ha. pose proof (IHb eta Heta) as Hb.
    destruct op; cbn [tr no_relative_atom Wa]; try tauto.
    destruct b; cbn [tr no_relative_atom] in *; tauto.
  - assert (Hpos : forall n, 0 < scons (bname (qd a)) eta n).
    { intros [|n]; cbn; [unfold bname; lia|apply Heta]. }
    destruct q; cbn [tr Wex no_relative_atom]; apply IHa; exact Hpos.
Qed.

(** The frozen source uses named output b and input a.  The concrete choice
    b=3, a=1 leaves even positive names available to Std_tr's binders. *)
Definition source_names (n : nat) : nat :=
  match n with 0 => 3 | 1 => 1 | S (S k) => 2 * k + 5 end.

Lemma source_names_positive n : 0 < source_names n.
Proof. destruct n as [|[|n]]; cbn [source_names]; lia. Qed.

Lemma source_names_injective n m : source_names n = source_names m -> n = m.
Proof. destruct n as [|[|n]], m as [|[|m]]; cbn [source_names]; lia. Qed.

Definition ordinary_code230 {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : nat :=
  padded230 (tr source_names phi).

Theorem ordinary_code230_decode {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  D (ordinary_code230 phi) = Wn (Wn (tr source_names phi)).
Proof.
  unfold ordinary_code230. apply D_padded230, tr_no_relative_atom.
  exact source_names_positive.
Qed.

Theorem ordinary_code230_fresh {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  fr (ordinary_code230 phi) (tr source_names phi) = false.
Proof.
  pose proof (D_private_fresh (ordinary_code230 phi)) as H.
  rewrite ordinary_code230_decode in H. exact H.
Qed.

Theorem ordinary_code230_core {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  leqv (D (gated230 1 3 (ordinary_code230 phi)))
    (KCore 1 3 (ordinary_code230 phi) (tr source_names phi)).
Proof.
  unfold ordinary_code230. apply padded_decoded_core_equiv.
  apply tr_no_relative_atom. exact source_names_positive.
Qed.
