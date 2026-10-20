(** Actual finite control steps of the first public unpair loop. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Read Program230Walk Program230Transition
 Program230Configurations Program230Histories Program230HistoryConstructors Program230HistoryJoin
 Program230TransferProgram Program230TransferStates Program230Copy2States Program230InstructionFormula
 Program230PairIteration Program230UnpairOuter.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_read_path_zeros M P n:
 program230_read M(program230_path_value M P)(P++repeat false n)(succM M(zeroM M)).
Proof.
 apply program230_read_app;exists(succM M(zeroM M));split;[apply program230_read_exact_path|].
 induction n as[|n IH];[reflexivity|]. cbn[repeat program230_read].
 exists(succM M(zeroM M));split;[left;repeat split;reflexivity|exact IH].
Qed.
Lemma program230_unpair_literal_step M P Q e s t:
 program230_pc s=program230_path_value M P->
 program230_read M(program230_path_value M P)Q(succM M(zeroM M))->
 fol p230(ENode(root p230))Q=Some e->is_node e=false->
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t)->
 Program230Histories.program230_step M p230_instruction_formula s t.
Proof.
 intros HP HR HF HE HS;apply p230_instruction_formula_correct.
 exists e,Q,(succM M(zeroM M));split;[split;[now rewrite HP|split;assumption]|exact HS].
Qed.
Section UnpairSteps.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation P:=p230_unpair_input_path.
Local Notation cfg:=(program230_copy2_state 8 6 7).
Local Ltac fields:=intros j Hj;rewrite !program230_copy2_register by exact Hj;
 do 9 (destruct j as[|j];[reflexivity|]);lia.
Local Ltac path:=f_equal;unfold p230_unpair_input_path;vm_compute;reflexivity.
Lemma program230_unpair_dec_input base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M P)(S n)x y)
 (cfg base(program230_path_value M(P++[true]))n x y).
Proof.
 eapply(program230_unpair_literal_step M P(P++[false])(EDecnz 8));[reflexivity| |vm_compute;reflexivity|reflexivity|].
 -apply program230_read_path_zero.
 -cbn[program230_edge_step];split;[lia|]. right;exists n;split.
  +rewrite program230_copy2_register by lia;reflexivity.
  +split;[path|fields].
Qed.
Lemma program230_unpair_inc_right base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true]))n x y)
 (cfg base(program230_path_value M(P++[true;true]))n x(S y)).
Proof.
 eapply(program230_unpair_literal_step M(P++[true])(P++[true;false])(EInc 7));[reflexivity| |vm_compute;reflexivity|reflexivity|].
 -replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zero.
 -cbn[program230_edge_step];split;[lia|]. split;[path|].
  rewrite program230_copy2_register by lia;fields.
Qed.
Lemma program230_unpair_dec_left_positive base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true]))n(S x)y)
 (cfg base(program230_path_value M(P++[true;true;false;false;true]))n x y).
Proof.
 eapply(program230_unpair_literal_step M(P++[true;true])(P++[true;true;false;false;false])(EDecnz 6));[reflexivity| |vm_compute;reflexivity|reflexivity|].
 -replace(P++[true;true;false;false;false])with((P++[true;true])++repeat false 3)
   by(rewrite <-app_assoc;reflexivity). apply program230_read_path_zeros.
 -cbn[program230_edge_step];split;[lia|]. right;exists x;split.
  +rewrite program230_copy2_register by lia;reflexivity.
  +split;[path|fields].
Qed.
Lemma program230_unpair_dec_left_zero base n y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true]))n Z y)
 (cfg base(program230_path_value M(P++[true;true;false;true]))n Z y).
Proof.
 eapply(program230_unpair_literal_step M(P++[true;true])(P++[true;true;false;false;false])(EDecnz 6));[reflexivity| |vm_compute;reflexivity|reflexivity|].
 -replace(P++[true;true;false;false;false])with((P++[true;true])++repeat false 3)
   by(rewrite <-app_assoc;reflexivity). apply program230_read_path_zeros.
 -cbn[program230_edge_step];split;[lia|]. left;split.
  +rewrite program230_copy2_register by lia;reflexivity.
  +split;[path|fields].
Qed.
Lemma program230_unpair_positive_break base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true;false;false;true]))n x y)
 (cfg base(program230_path_value M(P++[true;true;true]))n x y).
Proof.
 eapply(program230_unpair_literal_step M(P++[true;true;false;false;true])
 (P++[true;true;false;false;true])(EBreak 1));[reflexivity| |vm_compute;reflexivity|reflexivity|].
 -apply program230_read_exact_path.
 -cbn[program230_edge_step];split;[path|fields].
Qed.
Lemma program230_unpair_continue base n x y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true;true]))n x y)
 (cfg base(program230_path_value M P)n x y).
Proof.
 eapply(program230_unpair_literal_step M(P++[true;true;true])(P++[true;true;true])(EContinue 3));[reflexivity| |vm_compute;reflexivity|reflexivity|].
 -apply program230_read_exact_path.
 -cbn[program230_edge_step];split;[path|fields].
Qed.
Lemma program230_unpair_transfer_occurrence:
 program230_transfer_occurrence p230(P++[true;true;false;true])7 6 17 18.
Proof. split;[vm_compute;reflexivity|split;reflexivity]. Qed.
End UnpairSteps.
Print Assumptions program230_unpair_dec_input.
Print Assumptions program230_unpair_dec_left_positive.
Print Assumptions program230_unpair_transfer_occurrence.
