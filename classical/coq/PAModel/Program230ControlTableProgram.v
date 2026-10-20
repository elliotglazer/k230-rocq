(** Finite control-table certificates embed actual internal histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding Program230PathCode Program230Read
 Program230Walk Program230Edges Program230Transition Program230Configurations Program230Histories
 Program230TransferProgram Program230ControlTable.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_control_supported M p rows:=forall source Q e,In((source,Q),e)rows->
 exists rest,program230_read M(program230_path_value M source)Q rest /\
 fol p(ENode(root p))Q = Some e /\is_node e = false.
Lemma program230_control_table_in_program M p rows s t:
 program230_control_supported M p rows->
 Program230Histories.program230_step M(program230_control_table_formula rows)s t->
 Program230Transition.program230_step M p(program230_pc s)(program230_register s)(program230_register t)(program230_pc t).
Proof.
 intros HC HS;apply program230_control_table_correct in HS as[source[Q[e[HI[HP HE]]]]].
 destruct(HC source Q e HI)as[rest[HR[HF HL]]]. exists e,Q,rest;split;[|exact HE].
 split;[now rewrite HP|auto].
Qed.
Theorem program230_control_table_history M p rows b c N start:
 program230_control_supported M p rows->
 program230_history M(program230_control_table_formula rows)b c N start->
 program230_program_history M p b c N start.
Proof.
 intros HC[H0 HS];split;[exact H0|]. intros i s t Hi Hs Ht.
 apply(program230_control_table_in_program M p rows s t HC);exact(HS i s t Hi Hs Ht).
Qed.
Print Assumptions program230_control_table_history.
