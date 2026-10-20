(** Uniform finite controls for every literal unpair shape. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Read Program230Walk Program230Transition
 Program230Configurations Program230Histories Program230Copy2States Program230InstructionFormula
 Program230TransferProgram Program230UnpairControl Program230UnpairShape.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Section ShapeSteps.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Variable P:list bool.
Variables(a p0 p1 p2 p3 p4 p5 p6:nat).
Hypotheses(Ha:(a<9)%nat)(Ha6:a<>6)(Ha7:a<>7)
 (HO:program230_unpair_occurrence P a p0 p1 p2 p3 p4 p5 p6).
Local Notation cfg:=(program230_copy2_state a 6 7).
Local Ltac fields:=intros j Hj;rewrite !program230_copy2_register by exact Hj;
 destruct(Nat.eqb j a)eqn:EA;destruct(Nat.eqb j 6)eqn:E6;destruct(Nat.eqb j 7)eqn:E7;
 try(apply Nat.eqb_eq in EA);try(apply Nat.eqb_eq in E6);try(apply Nat.eqb_eq in E7);try congruence;reflexivity.
Local Ltac path:=rewrite program230_copy2_pc;f_equal;symmetry;first[
 apply program230_unpair_inc_input|apply program230_unpair_inc_right_path|
 apply program230_unpair_positive_path|apply program230_unpair_zero_path|
 apply program230_unpair_break_path|apply program230_unpair_continue_path].
Local Ltac reg_value:=rewrite program230_copy2_register by lia;
 rewrite ?Nat.eqb_refl;
 try rewrite(proj2(Nat.eqb_neq 6 a)ltac:(congruence));
 try rewrite(proj2(Nat.eqb_neq 7 a)ltac:(congruence));reflexivity.
Local Ltac leaves:=destruct(program230_unpair_occurrence_leaves P a p0 p1 p2 p3 p4 p5 p6 HO)
 as[HD[HI[HL[HB[HC HT]]]]].
Lemma program230_unpair_shape_dec_input base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M P)(S n)x y)
 (cfg base(program230_path_value M(P++[true]))n x y).
Proof.
 leaves; eapply(program230_unpair_literal_step M P(P++[false])(EDecnz a));[reflexivity| |assumption|reflexivity|].
 -apply program230_read_path_zero.
 -cbn[program230_edge_step];split;[lia|]. right;exists n;split.
  +reg_value.
  +split;[path|fields].
Qed.
Lemma program230_unpair_shape_inc_right base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true]))n x y)
 (cfg base(program230_path_value M(P++[true;true]))n x(S y)).
Proof.
 leaves; eapply(program230_unpair_literal_step M(P++[true])(P++[true;false])(EInc 7));[reflexivity| |assumption|reflexivity|].
 -replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zero.
 -cbn[program230_edge_step];split;[lia|]. split;[path|].
  rewrite program230_copy2_register by lia;
 rewrite(proj2(Nat.eqb_neq 7 a)ltac:(congruence));fields.
Qed.
Lemma program230_unpair_shape_dec_left_positive base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true]))n(S x)y)
 (cfg base(program230_path_value M(P++[true;true;false;false;true]))n x y).
Proof.
 leaves; eapply(program230_unpair_literal_step M(P++[true;true])(P++[true;true;false;false;false])(EDecnz 6));[reflexivity| |assumption|reflexivity|].
 -replace(P++[true;true;false;false;false])with((P++[true;true])++repeat false 3)
   by(rewrite <-app_assoc;reflexivity). apply program230_read_path_zeros.
 -cbn[program230_edge_step];split;[lia|]. right;exists x;split.
  +reg_value.
  +split;[path|fields].
Qed.
Lemma program230_unpair_shape_dec_left_zero base n y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true]))n Z y)
 (cfg base(program230_path_value M(P++[true;true;false;true]))n Z y).
Proof.
 leaves; eapply(program230_unpair_literal_step M(P++[true;true])(P++[true;true;false;false;false])(EDecnz 6));[reflexivity| |assumption|reflexivity|].
 -replace(P++[true;true;false;false;false])with((P++[true;true])++repeat false 3)
   by(rewrite <-app_assoc;reflexivity). apply program230_read_path_zeros.
 -cbn[program230_edge_step];split;[lia|]. left;split.
  +reg_value.
  +split;[path|fields].
Qed.
Lemma program230_unpair_shape_positive_break base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true;false;false;true]))n x y)
 (cfg base(program230_path_value M(P++[true;true;true]))n x y).
Proof.
 leaves; eapply(program230_unpair_literal_step M(P++[true;true;false;false;true])
 (P++[true;true;false;false;true])(EBreak 1));[reflexivity| |assumption|reflexivity|].
 -apply program230_read_exact_path.
 -cbn[program230_edge_step];split;[path|fields].
Qed.
Lemma program230_unpair_shape_continue base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true;true]))n x y)
 (cfg base(program230_path_value M P)n x y).
Proof.
 leaves; eapply(program230_unpair_literal_step M(P++[true;true;true])(P++[true;true;true])(EContinue 3));[reflexivity| |assumption|reflexivity|].
 -apply program230_read_exact_path.
 -cbn[program230_edge_step];split;[path|fields].
Qed.
Lemma program230_unpair_shape_transfer_occurrence:
 program230_transfer_occurrence p230(P++[true;true;false;true])7 6 p5 p6.
Proof. leaves;exact HT. Qed.
End ShapeSteps.
Print Assumptions program230_unpair_shape_dec_input.
Print Assumptions program230_unpair_shape_continue.
