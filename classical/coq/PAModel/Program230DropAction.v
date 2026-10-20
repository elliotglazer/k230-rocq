(** The literal DROP action is pushwff followed by loading parameter2. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions Pairing Program230PathCode
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230TransferStates Program230TransferProgram Program230Copy2Program Program230StackStates
 Program230PushParts Program230ParameterLoad Program230ParameterPushGeneric
 Program230RootHistory Program230Selector Program230SelectorReturn Program230SemanticHistories
 Program230PairConstructorIteration.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition p230_drop_push_path:=p230_selector_drop++[false].
Definition p230_drop_parameter_path:=p230_selector_drop++[true].
Definition p230_drop_action_exit:=inc_path(p230_drop_parameter_path++[true]).

Lemma p230_drop_push_shape:program230_push_shape p230_drop_push_path.
Proof.
 split.
 -exists 5009,5010;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
 -split.
  +exists 5012,5013;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
  +split.
   *split.
    --exists 5016,5017,5018;unfold program230_copy2_occurrence;vm_compute;repeat split;reflexivity.
    --split.
      ++exists 5022,5023;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
      ++vm_compute;repeat split;reflexivity.
   *exists 5024,5025;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
Qed.

Lemma p230_drop_parameter_shape:program230_parameter_shape p230_drop_parameter_path 5.
Proof.
 split.
 -exists 5027,5028,5029;unfold program230_copy2_occurrence;vm_compute;repeat split;reflexivity.
 -exists 5030,5031;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
Qed.

Lemma p230_drop_parameter_connector:
 ipeq p230_drop_parameter_path (inc_path(p230_drop_push_path++[true;true;true])).
Proof.
 unfold p230_drop_parameter_path,p230_drop_push_path,p230_selector_drop.
 vm_compute;unfold ipeq,bit;intro i.
 do 13(destruct i as[|i];[reflexivity|]);reflexivity.
Qed.

Theorem p230_drop_action_history M base tw ws value:
 pair_graph M tw ws value -> exists b c time,
 program230_history M p230_instruction_formula b c time
  (program230_stack_state base (program230_path_value M p230_selector_drop)
    tw ws (zeroM M) (zeroM M)) /\
 program230_state_at M b c time
  (program230_stack_state base (program230_path_value M p230_drop_action_exit)
    (program230_register base 5) value (zeroM M) (zeroM M)) /\
 coding_lt M (zeroM M) time.
Proof.
 intro Hpair.
 destruct (program230_parameter_push_history M p230_drop_push_path p230_drop_parameter_path 5
   base tw ws value ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
   p230_drop_push_shape p230_drop_parameter_shape p230_drop_parameter_connector Hpair)
   as [a [b [time [HR [HT Hpos]]]]].
 apply (proj2 (p230_instruction_history_correct M a b time _)) in HR.
 assert (Hnz:time<>zeroM M).
 {intro E;rewrite E in Hpos;destruct Hpos as [x Hx].
  rewrite coding_add_zero in Hx;exact (zero_ne_succ M x Hx). }
 destruct (p230_history_ipeq_endpoint M a b time
  (program230_stack_state base (program230_path_value M p230_drop_push_path)
    tw ws (zeroM M) (zeroM M))
  p230_drop_push_path p230_selector_drop
  (program230_stack_state base (program230_path_value M p230_drop_action_exit)
    (program230_register base 5) value (zeroM M) (zeroM M))
  eq_refl (ipeq_app_false p230_selector_drop) HR Hnz HT)
   as [d [e [HD [HE Hrest]]]].
 exists d,e,time;split;[exact HD|]. split;assumption.
Qed.

Lemma p230_drop_action_exit_ipeq:
 ipeq p230_drop_action_exit (inc_path p230_selector_drop).
Proof.
 unfold p230_drop_action_exit,p230_drop_parameter_path,p230_selector_drop.
 vm_compute;unfold ipeq,bit;intro i.
 do 13(destruct i as[|i];[reflexivity|]);reflexivity.
Qed.

Lemma p230_drop_stack_with_pc {D}(base:program230_configuration D)old pc tw ws a b:
 program230_with_pc (program230_stack_state base old tw ws a b) pc =
 program230_stack_state base pc tw ws a b.
Proof.
 apply program230_configuration_ext;intros j Hj.
 destruct j as [|i];[reflexivity|].
 change (program230_register (program230_with_pc
   (program230_stack_state base old tw ws a b) pc) i =
   program230_register (program230_stack_state base pc tw ws a b) i).
 rewrite program230_with_pc_register,!program230_stack_register by lia;reflexivity.
Qed.

Theorem p230_drop_action_returned M base tw ws value:
 pair_graph M tw ws value -> exists b c time,
 program230_history M p230_instruction_formula b c time
  (program230_stack_state base (program230_path_value M p230_selector_drop)
    tw ws (zeroM M) (zeroM M)) /\
 program230_state_at M b c time
  (program230_stack_state base (program230_path_value M p230_selector_return_exit)
    (program230_register base 5) value (zeroM M) (zeroM M)) /\
 coding_lt M (zeroM M) time.
Proof.
 intro HP;destruct (p230_drop_action_history M base tw ws value HP)
  as [a [b [time [HR [HT Hpos]]]]].
 set (out:=program230_stack_state base (program230_path_value M p230_drop_action_exit)
    (program230_register base 5) value (zeroM M) (zeroM M)) in *.
 destruct (p230_selector_drop_return M out) as [c [d [HC HD]]].
 assert (Hone:code_numeral M 1<>zeroM M).
 {intro E;exact (zero_ne_succ M (zeroM M) (eq_sym E)). }
 destruct (p230_history_ipeq_endpoint M c d (code_numeral M 1)
   (program230_with_pc out (program230_path_value M (inc_path p230_selector_drop)))
   (inc_path p230_selector_drop) p230_drop_action_exit
   (program230_with_pc out (program230_path_value M p230_selector_return_exit))
   eq_refl (ipeq_sym _ _ p230_drop_action_exit_ipeq) HC Hone HD)
   as [e [f [HE [HF Htail]]]].
 unfold out in HE;rewrite !p230_drop_stack_with_pc in HE.
 destruct (program230_history_join M p230_instruction_formula a b time e f (code_numeral M 1)
    _ out HR HT HE) as [g [h [HG [HL Hright]]]].
 exists g,h,(addM M time (code_numeral M 1));split;[exact HG|]. split.
 -unfold out in HF;rewrite p230_drop_stack_with_pc in HF.
  exact (proj1 (Hright (code_numeral M 1) _ (coding_lt_succ M (code_numeral M 1))) HF).
 -apply program230_duration_add;apply coding_lt_succ.
Qed.

Print Assumptions p230_drop_push_shape.
Print Assumptions p230_drop_parameter_shape.
Print Assumptions p230_drop_action_history.
Print Assumptions p230_drop_action_exit_ipeq.
Print Assumptions p230_drop_action_returned.
