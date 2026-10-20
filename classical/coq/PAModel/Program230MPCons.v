(** The exact implication constructor called by the public MP branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs Pairing Program230PathCode
 Program230Configurations Program230TransferProgram Program230Copy2Program Program230StackStates
 Program230Scale4Program Program230ConsTail Program230ConsGeneric Program230UnpairSites.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_mp_cons_path:list bool:=[true;true;true;true;false;false;true].
Lemma p230_mp_cons_shape:program230_cons_shape p230_mp_cons_path.
Proof.
 exists 5062,5069,5070;split.
 -apply nth_error_In with(n:=93);vm_compute;reflexivity.
 -split.
  +unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
  +split.
   *split.
    --exists 5073,5074,5075;unfold program230_copy2_occurrence;vm_compute;repeat split;reflexivity.
    --split.
      ++exists 5079,5080;unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity.
      ++vm_compute;repeat split;reflexivity.
   *split;[vm_compute;reflexivity|]. split.
    --intros j Hj;destruct j as[|[|[|[|j]]]];try lia;vm_compute;reflexivity.
    --vm_compute;reflexivity.
Qed.
Theorem p230_mp_cons_history M base tw stack x rest out:
 pair_graph M x rest stack->implication_graph M x tw out->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M p230_mp_cons_path)tw stack(zeroM M)(zeroM M)) /\
 program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(p230_mp_cons_path++[true;true])))out rest(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time.
Proof. apply(program230_cons_history M p230_mp_cons_path _ _ _ _ _ _ p230_mp_cons_shape). Qed.
Print Assumptions p230_mp_cons_shape.
Print Assumptions p230_mp_cons_history.
