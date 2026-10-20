(** The literal blank startup contains the exact physical initial register file.
    Its finite tape words satisfy the same graphs used for arbitrary internal
    register values and spare counts. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 PowerTwoSyntax PowerTwoRecurrence TM230UnaryBlocks TM230RegisterWords
 TM230SpareSyntax TM230SpareRecurrence TM230SpareBlocks
 TM230LiteralActions TM230BinaryStep TM230RunComposition TM230Paths TM230BitArithmetic
 TM230FiniteBoot TM230BootView.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith PArith setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.

Section Encoding.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation N := (code_numeral M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring finite_encoding_ring:(model_semiring M).
Ltac finite_encoding_constants := cbn[code_numeral];repeat multimatch goal with
 | |- context[succM M ?x]=>lazymatch x with
   | zeroM _=>fail 0
   | _=>rewrite(succ_as_add M x)
   end
 end.

Lemma finite_unary_block n tail :
 machine230_unary_block M (N n) (finite_word M tail)
   (finite_word M ((false::repeat true (S n))++tail)).
Proof.
 induction n as [|n IH].
 - apply(proj2(machine230_unary_block_zero M (finite_word M tail) _)).
   change(Z+N 2*(N 1+N 2*finite_word M tail)=N 2+N 4*finite_word M tail).
   finite_encoding_constants;ring.
 - change(machine230_unary_block M (succM M(N n)) (finite_word M tail)
     (finite_word M((false::repeat true(S(S n)))++tail))).
   replace(finite_word M((false::repeat true(S(S n)))++tail))
     with(N 2*finite_word M((false::repeat true(S n))++tail)+N 2).
   + now apply machine230_unary_block_successor_intro.
   + cbn [repeat app finite_word finite_bit machine230_bit].
     unfold finite_bit,machine230_bit. finite_encoding_constants;ring.
Qed.

Lemma finite_register_blocks values default tail :
 machine230_blocks_at M (length values)
   (fun idx=>N(nth idx values default)) (finite_word M tail)
   (finite_word M(B230.sepsR values++tail)).
Proof.
 induction values as [|v values IH].
 - reflexivity.
 - cbn [length machine230_blocks_at nth].
   exists(finite_word M(B230.sepsR values++tail));split;[exact IH|].
   replace(B230.sepsR(v::values)++tail)
     with((false::repeat true(S v))++(B230.sepsR values++tail))
     by(unfold B230.sepsR;cbn [flat_map];rewrite app_assoc;reflexivity).
   apply finite_unary_block.
Qed.

Lemma finite_spare_registers n :
 machine230_spare M (N n) (finite_word M(B230.sepsR(repeat 1 n))).
Proof.
 induction n as [|n IH].
 - apply machine230_spare_zero.
 - change(machine230_spare M (succM M(N n))
     (finite_word M(B230.sepsR(repeat 1(S n))))).
   apply(proj2(machine230_spare_prepend M (N n)
     (finite_word M(B230.sepsR(repeat 1 n))) _ IH)).
   change(machine230_unary_block M (N 1)
     (finite_word M(B230.sepsR(repeat 1 n)))
     (finite_word M((false::repeat true(S 1))++B230.sepsR(repeat 1 n)))).
   apply finite_unary_block.
Qed.

Definition machine230_initial_register idx :=
 N(if Nat.eqb idx 0 || Nat.eqb idx 4 then 3 else 0).

Lemma initial_register_physical_values idx :
 N(nth idx [0;0;0;3;0;0;3;0;0] 3)=
 machine230_initial_register(machine230_physical_register idx).
Proof.
 unfold machine230_initial_register,machine230_physical_register,machine230_physical_order.
 do 9 (destruct idx as [|idx];[reflexivity|]).
 destruct idx;reflexivity.
Qed.

Theorem machine230_boot_register_file :
 machine230_register_file M machine230_initial_register
  (finite_word M(B230.sepsR(repeat 1 167)))
  (finite_word M(B230.sepsR B230.boot_regs)).
Proof.
 pose proof(finite_register_blocks [0;0;0;3;0;0;3;0;0] 3
   (B230.sepsR(repeat 1 167)))as H.
 replace(B230.sepsR B230.boot_regs) with
   (B230.sepsR [0;0;0;3;0;0;3;0;0]++B230.sepsR(repeat 1 167))
   by(unfold B230.boot_regs,B230.sepsR;rewrite flat_map_app;reflexivity).
 unfold machine230_register_file.
 apply(proj1(machine230_blocks_ext M 9
   (fun idx=>N(nth idx [0;0;0;3;0;0;3;0;0] 3))
   (fun idx=>machine230_initial_register(machine230_physical_register idx))
   _ _ initial_register_physical_values)).
 exact H.
Qed.

Lemma finite_zero_prefix n tail : exists p,
 power2 M (N n) p /\
 finite_word M(repeat false n++tail)=p*finite_word M tail.
Proof.
 induction n as [|n [p[Hp HE]]].
 - exists(N 1);split;[apply power2_zero|].
   change(finite_word M tail=N 1*finite_word M tail). finite_encoding_constants;ring.
 - exists(N 2*p);split;[now apply power2_successor|].
   change(Z+N 2*finite_word M(repeat false n++tail)=N 2*p*finite_word M tail).
   rewrite HE. finite_encoding_constants;ring.
Qed.

Theorem machine230_uniform_initial_register_view :
 exists b c s p spare word,
  machine230_path M b c (N(Pos.to_nat 408419)) (machine230_seed M) s /\
  machine230_right_view M 84 (N 1) (p*(N 1+N 2*word)) s /\
  power2 M (N 181) p /\
  machine230_spare M (N 167) spare /\
  machine230_register_file M machine230_initial_register spare word.
Proof.
 destruct(machine230_uniform_dispatch_entry M)as[b[c[s[HP HV]]]].
 destruct(finite_zero_prefix 181 (true::B230.sepsR B230.boot_regs))as[p[Hp HE]].
 exists b,c,s,p,(finite_word M(B230.sepsR(repeat 1 167))),
   (finite_word M(B230.sepsR B230.boot_regs)).
 split;[exact HP|]. split.
 - change(machine230_right_view M 84 (N 1)
     (p*finite_word M(true::B230.sepsR B230.boot_regs))s).
   rewrite <-HE. exact HV.
 - split;[exact Hp|]. split;[apply finite_spare_registers|apply machine230_boot_register_file].
Qed.
End Encoding.
Print Assumptions finite_unary_block.
Print Assumptions finite_spare_registers.
Print Assumptions machine230_boot_register_file.
Print Assumptions machine230_uniform_initial_register_view.
