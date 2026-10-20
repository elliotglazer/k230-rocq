(** The uniform blank startup in the dispatcher's actual right-tape view. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  TM230BinaryStep TM230RunComposition TM230Paths TM230BitArithmetic
  TM230FiniteBoot TM230BootLength.
From Stdlib Require Import Lists.List setoid_ring.Ring PArith.
Import ListNotations.
Unset Implicit Arguments.

Lemma finite_config_right_view M q l r :
  machine230_right_view M q (finite_word M l) (finite_word M r)
    (finite_config M (q,l,r)).
Proof.
  unfold machine230_right_view,finite_config.
  cbn [machine230_state machine230_left machine230_head machine230_right].
  split; [reflexivity|]. split; [reflexivity|]. split.
  - destruct (hd false r); [right|left]; reflexivity.
  - rewrite (finite_word_split M r).
    rewrite (Arithmetic.add_comm M). reflexivity.
Qed.

Lemma finite_word_single M b : finite_word M [b] = finite_bit M b.
Proof.
  change (addM M (finite_bit M b)
    (mulM M (code_numeral M 2) (zeroM M)) = finite_bit M b).
  rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,coding_add_zero_r.
  reflexivity.
Qed.

Theorem machine230_boot_right_view M :
  machine230_right_view M 84 (code_numeral M 1) (finite_word M B230.boot_right)
    (machine230_boot_config M).
Proof.
  pose proof (finite_config_right_view M 84 [true] B230.boot_right) as H.
  rewrite finite_word_single in H. exact H.
Qed.

Theorem machine230_uniform_dispatch_entry M :
  exists b c s,
    machine230_path M b c (code_numeral M (Pos.to_nat 408419))
      (machine230_seed M) s /\
    machine230_right_view M 84 (code_numeral M 1) (finite_word M B230.boot_right) s.
Proof.
  destruct (machine230_uniform_boot_exact M) as [b [c H]].
  exists b,c,(machine230_boot_config M). split; [exact H|].
  apply machine230_boot_right_view.
Qed.

Print Assumptions machine230_boot_right_view.
Print Assumptions machine230_uniform_dispatch_entry.
