(** The actual balanced multiplier-four loop and its complete internal run. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions Program230PathCode Program230Read Program230Walk
 Program230Configurations Program230Histories Program230TransferProgram Program230Copy2Program Program230ControlTable
 Program230ControlTableProgram Program230Scale4States Program230Scale4Loop.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_read_zero_repeat M n:
 program230_read M(succM M(zeroM M))(repeat false n)(succM M(zeroM M)).
Proof. induction n;[reflexivity|]. cbn[repeat program230_read].
 exists(succM M(zeroM M));split;[left;repeat split;reflexivity|exact IHn]. Qed.
Lemma program230_read_path_zeros M P n:
 program230_read M(program230_path_value M P)(P++repeat false n)(succM M(zeroM M)).
Proof. apply program230_read_app;exists(succM M(zeroM M));split;
 [apply program230_read_exact_path|apply program230_read_zero_repeat]. Qed.
Definition program230_scale4_leaves p P a b:=
 fol p(ENode(root p))(P++[false]) = Some(EDecnz a) /\
 (forall j,(j<4)%nat->fol p(ENode(root p))(program230_scale4_leaf P j) = Some(EInc b)) /\
 fol p(ENode(root p))(P++[true;true]) = Some(EContinue 2).
Lemma program230_scale4_supported M p P a b:
 program230_scale4_leaves p P a b->program230_control_supported M p(program230_scale4_rows P a b).
Proof.
 intros[HD[HI HC]]source Q e H;unfold program230_scale4_rows in H.
 destruct H as[E|[E|[E|[E|[E|[E|[]]]]]]];inversion E;subst source Q e.
 -exists(succM M(zeroM M));split;[apply program230_read_path_zero|]. split;[exact HD|reflexivity].
 -exists(succM M(zeroM M));split;[|split;[exact(HI 0 ltac:(lia))|reflexivity]].
  unfold program230_scale4_pc,program230_scale4_leaf;cbn[Nat.eqb].
  replace(P++[true;false;false;false])with((P++[true])++repeat false 3)
   by(repeat rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zeros.
 -exists(succM M(zeroM M));split;[apply program230_read_exact_path|]. split;[exact(HI 1 ltac:(lia))|reflexivity].
 -exists(succM M(zeroM M));split;[apply program230_read_exact_path|]. split;[exact(HI 2 ltac:(lia))|reflexivity].
 -exists(succM M(zeroM M));split;[apply program230_read_exact_path|]. split;[exact(HI 3 ltac:(lia))|reflexivity].
 -exists(program230_path_value M[false;false]);split;[|split;[exact HC|reflexivity]].
  unfold program230_scale4_pc.
  replace(P++[true;true;false;false])with((P++[true;true])++[false;false])
   by(repeat rewrite <-app_assoc;reflexivity).
  apply program230_read_concat_path.
Qed.
Theorem program230_scale4_program_history M p P a b start count:
 (a<9)%nat->(b<9)%nat->a<>b->program230_scale4_leaves p P a b->
 program230_pc start = program230_path_value M P->program230_register start a = count->
 exists u v final,program230_program_history M p u v(program230_scale4_time M count)start /\
 program230_state_at M u v(program230_scale4_time M count)final /\
 program230_pc final = program230_path_value M(inc_path P) /\program230_register final a = zeroM M /\
 program230_register final b = addM M(program230_register start b)(mulM M(code_numeral M 4)count) /\
 (forall i,(i<9)%nat->i<>a->i<>b->program230_register final i = program230_register start i).
Proof.
 intros Ha Hb Hab HF HP HA.
 destruct(program230_scale4_loop M P a b Ha Hb Hab start count HP HA)as[u[v[final[HR HT]]]].
 exists u,v,final;split;[|exact HT].
 exact(program230_control_table_history M p(program230_scale4_rows P a b)u v(program230_scale4_time M count)start
 (program230_scale4_supported M p P a b HF)HR).
Qed.
Definition p230_scale4_path:list bool:=[true;true;true;false;true;false;false;true;false;false;true;false;false;true;false;true;true].
Lemma p230_scale4_exact:program230_scale4_leaves p230 p230_scale4_path 7 1.
Proof. split;[vm_compute;reflexivity|]. split.
 -intros j Hj;destruct j as[|[|[|[|j]]]];try lia;vm_compute;reflexivity.
 -vm_compute;reflexivity.
Qed.
Theorem p230_scale4_history M start count:
 program230_pc start = program230_path_value M p230_scale4_path->program230_register start 7 = count->
 exists u v final,program230_program_history M p230 u v(program230_scale4_time M count)start /\
 program230_state_at M u v(program230_scale4_time M count)final /\
 program230_pc final = program230_path_value M(inc_path p230_scale4_path) /\program230_register final 7 = zeroM M /\
 program230_register final 1 = addM M(program230_register start 1)(mulM M(code_numeral M 4)count) /\
 (forall i,(i<9)%nat->i<>7->i<>1->program230_register final i = program230_register start i).
Proof. apply(program230_scale4_program_history M p230 p230_scale4_path 7 1 start count);try lia;exact p230_scale4_exact. Qed.
Print Assumptions program230_scale4_program_history.
Print Assumptions p230_scale4_exact.
Print Assumptions p230_scale4_history.
