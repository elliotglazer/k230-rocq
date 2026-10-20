(** Exact post-transfer continuation, including its stored trailing zero bit. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Read Program230Walk Program230Transition
 Program230Configurations Program230Histories Program230Copy2States Program230Copy2Program
 Program230InstructionFormula Program230UnpairOuter Program230UnpairControl Program230UnpairShape.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_unpair_shape_transfer_return M P a p0 p1 p2 p3 p4 p5 p6:
 program230_unpair_occurrence P a p0 p1 p2 p3 p4 p5 p6->forall base n x y,
 Program230Histories.program230_step M p230_instruction_formula
 (program230_copy2_state a 6 7 base
  (program230_path_value M(P++[true;true;true;false]))n x y)
 (program230_copy2_state a 6 7 base(program230_path_value M P)n x y).
Proof.
 intros HO base n x y.
 destruct(program230_unpair_occurrence_leaves P a p0 p1 p2 p3 p4 p5 p6 HO)as[HD[HI[HL[HB[HC HT]]]]].
 apply p230_instruction_formula_correct.
 exists(EContinue 3),(P++[true;true;true]),(program230_path_value M[false]).
 split.
 -split.
  +change(program230_read M(program230_path_value M(P++[true;true;true;false]))
    (P++[true;true;true])(program230_path_value M[false])).
   replace(P++[true;true;true;false])
   with((P++[true;true;true])++[false])by(rewrite <-app_assoc;reflexivity).
   apply program230_read_concat_path.
  +split;[exact HC|reflexivity].
 -cbn[program230_edge_step];split.
  +change(program230_path_value M P=
    program230_path_value M(cont 3(P++[true;true;true]))).
   f_equal;symmetry;apply program230_unpair_continue_path.
  +intros i Hi;rewrite !program230_copy2_register by exact Hi;reflexivity.
Qed.
Print Assumptions program230_unpair_shape_transfer_return.
