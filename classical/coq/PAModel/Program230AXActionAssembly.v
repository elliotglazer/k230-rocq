(** Compose the exact364 AX constructor rows with the actual final equality gate.
    The sole implementation family is explicit here; the literal row-runtime
    module discharges it separately. No path padding is equated arithmetically. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions NumericalProofs SearchStep
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230PathCode Program230RootHistory Program230TransferStates Program230TransferEntry
 Program230AXSymbolic Program230AXSymbolicGraphs Program230AXPathSchedule Program230AXPublicFold
 Program230AXGateSites Program230AXGateReload Program230AXGate Program230AXContract
 Program230Selector Program230SelectorReturn Program230UnpairRestore.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition p230_ax_action_environment M (start:program230_configuration(carrier M)) y pl4 u pl5 b : nat->carrier M:=
 fun i=>match i with
 |0=>program230_register start 4 |1=>program230_register start 5 |2=>b
 |3=>program230_register start 3 |4=>u |5=>program230_register start 1
 |6=>program230_register start 2 |7=>program230_register start 0
 |8=>program230_register start 8 |9=>pl4 |10=>pl5 |11=>y |_=>zeroM M end.

Lemma p230_ax_action_initial_graph M start y pl4 u pl5 b:
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 p230_ax_register_graph M (p230_ax_action_environment M start y pl4 u pl5 b)
 p230_ax_symbolic_initial start.
Proof.
 intros H6 H7 i Hi;do 9(destruct i as[|i];[try reflexivity;try exact H6;try exact H7|]);lia.
Qed.

Lemma p230_ax_action_gate_entry M last finalpath c a b:
 program230_pc last=program230_path_value M finalpath ->
 program230_register last 3=c ->program230_register last 4=a ->program230_register last 5=b ->
 program230_register last 6=zeroM M ->program230_register last 7=zeroM M ->
 program230_with_pc
 (p230_ax_gate_state M last(program230_path_value M p230_ax_gate_copy)c a b
  (program230_register last 1)(zeroM M)(zeroM M))
 (program230_path_value M finalpath)=last.
Proof.
 intros HP H3 H4 H5 H6 H7;apply program230_configuration_ext;intros j Hj.
 destruct j as[|j];[exact(eq_sym HP)|].
 change(program230_register
 (program230_with_pc(p230_ax_gate_state M last(program230_path_value M p230_ax_gate_copy)c a b
 (program230_register last 1)(zeroM M)(zeroM M))(program230_path_value M finalpath))j=
 program230_register last j).
 rewrite program230_with_pc_register.
 do 9(destruct j as[|j];[try reflexivity;try exact(eq_sym H3);try exact(eq_sym H4);
 try exact(eq_sym H5);try exact(eq_sym H6);try exact(eq_sym H7)|]);lia.
Qed.

Theorem p230_ax_action_from_public_rows M:
 (forall env,
  env 2=addM M(env 1)(env 11)->
  pair_graph M(env 11)(env 9)(env 8)->
  pair_graph M(env 4)(env 10)(env 9)->
  p230_ax_public_row_implementations M env)->
 p230_ax_action_contract M.
Proof.
 intros Hrows start y pl4 u pl5 b top stack HP H6 H7 Hpair Hpair' Hb Hstack Hout.
 set(env:=p230_ax_action_environment M start y pl4 u pl5 b).
 assert(Himpl:p230_ax_public_row_implementations M env).
 {apply Hrows;[exact Hb|exact Hpair|exact Hpair']. }
 assert(HG:p230_ax_register_graph M env p230_ax_symbolic_initial start).
 {apply p230_ax_action_initial_graph;assumption. }
 assert(Hroot:program230_pc start=program230_path_value M p230_ax_schedule_root)by exact HP.
 destruct(p230_ax_public_history_fold M env start Himpl Hroot HG)
 as[d[e[N[last[finalpath[HR[HT[HN[HL[Hpath HF]]]]]]]]]].
 destruct(p230_ax_symbolic_final_graphs M env last HF)
 as[Hbundle[Hstack'[H0[H3[H4[H5[H6'[H7' H8]]]]]]]].
 change(search_bundle M(program230_register start 4)b(program230_register start 3)
 (program230_register last 1))in Hbundle.
 change(search_stack M(program230_register start 4)(program230_register start 5)b
 (program230_register start 3)u(program230_register start 1)(program230_register start 2)
 (program230_register last 2))in Hstack'.
 change(program230_register last 0=program230_register start 0)in H0.
 change(program230_register last 3=program230_register start 3)in H3.
 change(program230_register last 4=program230_register start 4)in H4.
 change(program230_register last 5=b)in H5.
 change(program230_register last 8=pl5)in H8.
 assert(ES:program230_register last 2=stack).
 {unfold search_stack in Hstack,Hstack';eapply code_relation_functional;[exact Hstack'|exact Hstack]. }
 assert(Hgate:(((program230_register start 3=program230_register start 4 \/
 program230_register start 3=b)/\top=zeroM M)\/
 (program230_register start 3<>program230_register start 4 /\program230_register start 3<>b /\
 top=program230_register last 1))).
 {destruct Hout as[Hbad|[Ha[Hbb HB]]];[left;exact Hbad|right;split;[exact Ha|];split;[exact Hbb|]].
  unfold search_bundle in HB,Hbundle;eapply code_relation_functional;[exact HB|exact Hbundle]. }
 destruct(p230_ax_gate_history M last(program230_register start 4)b(program230_register start 3)
 (program230_register last 1)top Hgate)as[f[g[K[HK[HKlast HKpos]]]]].
 assert(HKnonzero:K<>zeroM M).
 {intro E;rewrite E in HKpos;destruct HKpos as[t Ht];rewrite coding_add_zero in Ht;exact(zero_ne_succ M t Ht). }
 assert(Hgatepath:ipeq p230_ax_gate_copy finalpath).
 {change(ipeq p230_ax_schedule_gate finalpath);exact(ipeq_sym _ _ Hpath). }
 destruct(p230_history_ipeq_endpoint M f g K
 (p230_ax_gate_state M last(program230_path_value M p230_ax_gate_copy)(program230_register start 3)
 (program230_register start 4)b(program230_register last 1)(zeroM M)(zeroM M))
 p230_ax_gate_copy finalpath
 (p230_ax_gate_state M last(program230_path_value M p230_selector_return_exit)
 (zeroM M)(zeroM M)(zeroM M)top(zeroM M)(zeroM M))
 eq_refl Hgatepath HK HKnonzero HKlast)as[h[i[HI[HIl _]]]].
 rewrite(p230_ax_action_gate_entry M last finalpath(program230_register start 3)
 (program230_register start 4)b HL H3 H4 H5 H6' H7')in HI.
 assert(EL:p230_ax_gate_state M last(program230_path_value M p230_selector_return_exit)
 (zeroM M)(zeroM M)(zeroM M)top(zeroM M)(zeroM M)=p230_ax_result M start top stack pl5).
 {apply program230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
  change(program230_register
  (p230_ax_gate_state M last(program230_path_value M p230_selector_return_exit)
   (zeroM M)(zeroM M)(zeroM M)top(zeroM M)(zeroM M))j=
  program230_register(p230_ax_result M start top stack pl5)j).
  do 9(destruct j as[|j];[try reflexivity;try exact H0;try exact ES;try exact H8|]);lia. }
 rewrite EL in HIl.
 destruct(program230_history_join M p230_instruction_formula d e N h i K start last HR HT HI)
 as[j[k[HJ[Hleft Hright]]]].
 exists j,k,(addM M N K);split;[exact HJ|];split.
 -exact(proj1(Hright K _(coding_lt_succ M K))HIl).
 -apply program230_positive_sum;exact HN.
Qed.
Print Assumptions p230_ax_action_initial_graph.
Print Assumptions p230_ax_action_gate_entry.
Print Assumptions p230_ax_action_from_public_rows.

