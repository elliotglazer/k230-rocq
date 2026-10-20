(** Spare recurrence agrees with the exact value-one register block. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 PowerTwoSyntax TM230UnaryBlocks TM230SpareSyntax TM230SpareRecurrence TM230SparePower.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Blocks.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring spare_blocks_ring:(model_semiring M).
Ltac spare_block_constants := cbn[code_numeral];repeat multimatch goal with
 | |- context[succM M ?x]=>lazymatch x with
   | zeroM _=>fail 0
   | _=>rewrite(succ_as_add M x)
   end
 end.
Theorem machine230_unary_block_one tail word:
 machine230_unary_block M(N 1)tail word <->word=N 6+N 8*tail.
Proof.
 assert(H0:machine230_unary_block M Z tail(N 2+N 4*tail)).
 {apply(proj2(machine230_unary_block_zero M tail _));reflexivity. }
 replace(N 6+N 8*tail)with(N 2*(N 2+N 4*tail)+N 2)by(spare_block_constants;ring).
 exact(machine230_unary_block_successor M Z tail(N 2+N 4*tail)word H0).
Qed.
Theorem machine230_spare_prepend n old next:
 machine230_spare M n old ->
 (machine230_spare M(S n)next<->machine230_unary_block M(N 1)old next).
Proof.
 intro H. rewrite(machine230_spare_successor_iff M n old next H).
 now rewrite machine230_unary_block_one.
Qed.
Theorem machine230_spare_append_block n old p:
 machine230_spare M n old ->power2 M(N 3*n)p->
 machine230_unary_block M(N 1)old(old+N 6*p).
Proof.
 intros H Hp. apply(proj1(machine230_spare_prepend n old _ H)).
 exact(machine230_spare_append M n old p H Hp).
Qed.
End Blocks.
Print Assumptions machine230_unary_block_one.
Print Assumptions machine230_spare_prepend.
Print Assumptions machine230_spare_append_block.
