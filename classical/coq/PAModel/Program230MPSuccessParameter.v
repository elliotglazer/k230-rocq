(** Exact parameter-1 construction on the equal continuation of the public MP branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230TransferProgram Program230Copy2Program Program230StackStates
 Program230PushParts Program230ParameterLoad Program230ParameterPushGeneric.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_mp_success_push_path:list bool:=[true;true;true;true;true;true;false].
Definition p230_mp_success_parameter_path:list bool:=[true;true;true;true;true;true;true].
Lemma p230_mp_success_push_shape:program230_push_shape p230_mp_success_push_path.
Proof.
 split.
 -exists 5101,5102;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
 -split.
  +exists 5104,5105;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
  +split.
   *split.
    --exists 5108,5109,5110;unfold program230_copy2_occurrence;vm_compute;repeat split;reflexivity.
    --split.
      ++exists 5114,5115;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
      ++vm_compute;repeat split;reflexivity.
   *exists 5116,5117;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
Qed.
Lemma p230_mp_success_parameter_shape:program230_parameter_shape p230_mp_success_parameter_path 4.
Proof. split.
 -exists 5119,5120,5121;unfold program230_copy2_occurrence;vm_compute;repeat split;reflexivity.
 -exists 5122,5123;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
Qed.
Lemma p230_mp_success_parameter_connector:ipeq p230_mp_success_parameter_path(inc_path(p230_mp_success_push_path++[true;true;true])).
Proof. unfold p230_mp_success_parameter_path,p230_mp_success_push_path;vm_compute;unfold ipeq,bit;intro i.
 do 13(destruct i as[|i];[reflexivity|]);reflexivity. Qed.
Theorem p230_mp_success_parameter_history M base tw ws value:
 pair_graph M tw ws value->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M p230_mp_success_push_path)tw ws(zeroM M)(zeroM M)) /\
 Program230Configurations.program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(p230_mp_success_parameter_path++[true])))
   (program230_register base 4)value(zeroM M)(zeroM M)) /\coding_lt M(zeroM M)time.
Proof.
 apply(program230_parameter_push_history M p230_mp_success_push_path p230_mp_success_parameter_path 4 base tw ws value);
 try lia;[exact p230_mp_success_push_shape|exact p230_mp_success_parameter_shape|exact p230_mp_success_parameter_connector].
Qed.
Print Assumptions p230_mp_success_parameter_history.
