(** The positive sentinel PC code is distinct from a binary tape word.
    Their exact affine relation is proved for every literal path in every model. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BitArithmetic TM230DispatchWords
 Program230PathCode PowerTwoSyntax PowerTwoRecurrence.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section Bits.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_dispatch_code_ring:(model_semiring M).
Theorem machine230_dispatch_path_code P:
 program230_path_value M P=machine230_dispatch_bits M P one.
Proof. induction P as[|b P IH];cbn[program230_path_value machine230_dispatch_bits];[reflexivity|now rewrite IH]. Qed.
Theorem machine230_dispatch_bits_append P Q tail:
 machine230_dispatch_bits M(P++Q)tail=machine230_dispatch_bits M P(machine230_dispatch_bits M Q tail).
Proof. induction P as[|b P IH];cbn[app machine230_dispatch_bits];[reflexivity|now rewrite IH]. Qed.
Theorem machine230_dispatch_bits_linear P p tail:
 power2 M(N(length P))p ->
 machine230_dispatch_bits M P tail=machine230_dispatch_bits M P Z+p*tail.
Proof.
 revert p. induction P as[|b P IH];intros p HP.
 -rewrite(power2_zero_value M p HP). cbn[machine230_dispatch_bits]. rewrite Arithmetic.mul_one,Arithmetic.add_zero;reflexivity.
 -change(power2 M(S(N(length P)))p)in HP.
  destruct(power2_successor_inv M(N(length P))p HP)as[q[HQ Ep]]. change(p=two*q)in Ep.
  cbn[machine230_dispatch_bits]. rewrite(IH q HQ),Ep;ring.
Qed.
Theorem machine230_dispatch_pc_word_relation P p tail:
 power2 M(N(length P))p ->
 machine230_dispatch_bits M P tail+p=program230_path_value M P+p*tail.
Proof.
 intro HP;rewrite machine230_dispatch_path_code,(machine230_dispatch_bits_linear P p tail HP),
  (machine230_dispatch_bits_linear P p one HP);ring.
Qed.
Lemma machine230_zero_bits count:machine230_dispatch_bits M(repeat false count)Z=Z.
Proof.
 induction count;cbn[repeat machine230_dispatch_bits];[reflexivity|]. rewrite IHcount.
 change(Z+two*Z=Z);ring.
Qed.
Theorem machine230_dispatch_zero_bits count p tail:
 power2 M(N count)p->machine230_dispatch_bits M(repeat false count)tail=p*tail.
Proof.
 intro HP. rewrite(machine230_dispatch_bits_linear(repeat false count)p tail ltac:(now rewrite repeat_length)).
 rewrite machine230_zero_bits,Arithmetic.add_zero;reflexivity.
Qed.
Theorem machine230_dispatch_zero_suffix P Q count p tail:
 P=Q++repeat false count ->power2 M(N count)p ->
 machine230_dispatch_bits M P tail=machine230_dispatch_bits M Q(p*tail).
Proof. intros -> HP;rewrite machine230_dispatch_bits_append,(machine230_dispatch_zero_bits count p tail HP);reflexivity. Qed.
End Bits.
Print Assumptions machine230_dispatch_path_code.
Print Assumptions machine230_dispatch_bits_linear.
Print Assumptions machine230_dispatch_pc_word_relation.
Print Assumptions machine230_dispatch_zero_suffix.
