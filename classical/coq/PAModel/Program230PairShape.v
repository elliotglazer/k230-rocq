(** Finite shape certificates for every actual pair162 occurrence. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Read Program230Walk Program230Transition
 Program230Configurations Program230Histories Program230TransferStates Program230Copy2States
 Program230Copy2Program Program230TransferProgram Program230Scale4Program Program230InstructionFormula
 Program230PairConstructorIteration.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_pair_shape P :=
 (exists n m k,program230_copy2_occurrence p230(P++[false])1 7 6 n m k) /\
 (exists n m,program230_transfer_occurrence p230(P++[true;true;false;true])6 1 n m) /\
 fol p230(ENode(root p230))(P++[true;false])=Some(EDecnz 6) /\
 fol p230(ENode(root p230))(P++[true;true;false;false])=Some(EInc 7) /\
 fol p230(ENode(root p230))(P++[true;true;true])=Some(EContinue 3).
Lemma program230_pair_dec_path P:inc_path(P++[true;false])=P++[true;true].
Proof. replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_false,<-app_assoc;reflexivity. Qed.
Lemma program230_pair_exit_path P:brk 1(P++[true;false])=(inc_path P)++[false].
Proof. replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
 rewrite brk_car1,inc_path_app_true;reflexivity. Qed.
Lemma program230_pair_inc_path P:inc_path(P++[true;true;false;false])=P++[true;true;false;true].
Proof. replace(P++[true;true;false;false])with((P++[true;true;false])++[false])by(rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_false,<-app_assoc;reflexivity. Qed.
Lemma program230_pair_transfer_path P:inc_path(P++[true;true;false;true])=P++[true;true;true;false].
Proof. replace(P++[true;true;false;true])with((P++[true;true;false])++[true])by(rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_true.
 replace(P++[true;true;false])with((P++[true;true])++[false])by(rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_false;repeat rewrite <-app_assoc;reflexivity. Qed.
Lemma program230_pair_continue_path P:cont 3(P++[true;true;true])=P.
Proof. replace(P++[true;true;true])with(((P++[true])++[true])++[true])by(repeat rewrite <-app_assoc;reflexivity).
 rewrite !cont_cdrS,cont_cdr1;reflexivity. Qed.
Lemma program230_pair_literal_step M P Q e s t:
 program230_pc s=program230_path_value M P ->
 program230_read M(program230_path_value M P)Q(succM M(zeroM M))->
 fol p230(ENode(root p230))Q=Some e ->is_node e=false->
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t)->
 Program230Histories.program230_step M p230_instruction_formula s t.
Proof.
 intros HP HR HF HE HS;apply p230_instruction_formula_correct.
 exists e,Q,(succM M(zeroM M));split;[split;[now rewrite HP|split;assumption]|exact HS].
Qed.
Section Control.
Variable M:Model.
Variable P:list bool.
Hypothesis Hshape:program230_pair_shape P.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation cfg:=program230_pair_state.
Local Ltac fields:=intros j Hj;unfold program230_pair_state;rewrite !program230_copy2_register by exact Hj;
 do 9(destruct j as[|j];[reflexivity|]);lia.
Lemma program230_pair_shape_dec_positive base k z:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true]))(S k)Z z)
 (cfg base(program230_path_value M(P++[true;true]))k Z z).
Proof.
 destruct Hshape as[_[_[HD _]]].
 eapply(program230_pair_literal_step M(P++[true])(P++[true;false])(EDecnz 6));[reflexivity| |exact HD|reflexivity|].
 -replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zero.
 -cbn[program230_edge_step];split;[lia|]. right;exists k;split.
  +unfold program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  +split;[rewrite program230_pair_dec_path;reflexivity|fields].
Qed.
Lemma program230_pair_shape_dec_zero base z:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true]))Z Z z)
 (cfg base(program230_path_value M((inc_path P)++[false]))Z Z z).
Proof.
 destruct Hshape as[_[_[HD _]]].
 eapply(program230_pair_literal_step M(P++[true])(P++[true;false])(EDecnz 6));[reflexivity| |exact HD|reflexivity|].
 -replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zero.
 -cbn[program230_edge_step];split;[lia|]. left;split.
  +unfold program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  +split;[rewrite program230_pair_exit_path;reflexivity|fields].
Qed.
Lemma program230_pair_shape_inc base k z:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true]))k Z z)
 (cfg base(program230_path_value M(P++[true;true;false;true]))k Z(S z)).
Proof.
 destruct Hshape as[_[_[_[HI _]]]].
 eapply(program230_pair_literal_step M(P++[true;true])(P++[true;true;false;false])(EInc 7));[reflexivity| |exact HI|reflexivity|].
 -replace(P++[true;true;false;false])with((P++[true;true])++repeat false 2)by(rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zeros.
 -cbn[program230_edge_step];split;[lia|]. split;[rewrite program230_pair_inc_path;reflexivity|].
  unfold program230_pair_state;rewrite program230_copy2_register by lia;fields.
Qed.
Lemma program230_pair_shape_continue base k z:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true;true;false]))Z k z)
 (cfg base(program230_path_value M P)Z k z).
Proof.
 destruct Hshape as[_[_[_[_ HC]]]]. apply p230_instruction_formula_correct.
 exists(EContinue 3),(P++[true;true;true]),(program230_path_value M[false]);split.
 -split;[|split;[exact HC|reflexivity]].
  change(program230_read M(program230_path_value M(P++[true;true;true;false]))(P++[true;true;true])(program230_path_value M[false])).
  replace(P++[true;true;true;false])with((P++[true;true;true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply program230_read_concat_path.
 -cbn[program230_edge_step];split;[rewrite program230_pair_continue_path;reflexivity|fields].
Qed.
End Control.
Print Assumptions program230_pair_shape_dec_positive.
Print Assumptions program230_pair_shape_continue.
