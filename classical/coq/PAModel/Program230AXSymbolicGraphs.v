(** Arithmetic graph projections for the verified symbolic AX result. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SearchStep
 Program230Configurations Program230AXCompactSchedule Program230AXSymbolic.
From Stdlib Require Import Arith.Arith Lia.
Unset Implicit Arguments.
Definition p230_ax_register_graph M env(symbolic:program230_configuration code_expr)(actual:program230_configuration(carrier M)):=
 forall i,(i<9)%nat->code_relation M env(program230_register symbolic i)(program230_register actual i).
Theorem p230_ax_register_graph_total M env symbolic pc:
 exists actual,program230_pc actual=pc /\p230_ax_register_graph M env symbolic actual.
Proof.
 destruct(code_relation_total M(program230_register symbolic 0)env)as[r0 H0].
 destruct(code_relation_total M(program230_register symbolic 1)env)as[r1 H1].
 destruct(code_relation_total M(program230_register symbolic 2)env)as[r2 H2].
 destruct(code_relation_total M(program230_register symbolic 3)env)as[r3 H3].
 destruct(code_relation_total M(program230_register symbolic 4)env)as[r4 H4].
 destruct(code_relation_total M(program230_register symbolic 5)env)as[r5 H5].
 destruct(code_relation_total M(program230_register symbolic 6)env)as[r6 H6].
 destruct(code_relation_total M(program230_register symbolic 7)env)as[r7 H7].
 destruct(code_relation_total M(program230_register symbolic 8)env)as[r8 H8].
 exists(mkProgram230Configuration(carrier M)pc r0 r1 r2 r3 r4 r5 r6 r7 r8);split;[reflexivity|].
 intros i Hi;do 9(destruct i as[|i];[assumption|]);lia.
Qed.
Theorem p230_ax_symbolic_final_graphs M env actual:
 p230_ax_register_graph M env p230_ax_symbolic_final actual->
 search_bundle M(env 0)(env 2)(env 3)(program230_register actual 1) /\
 search_stack M(env 0)(env 1)(env 2)(env 3)(env 4)(env 5)(env 6)(program230_register actual 2) /\
 program230_register actual 0=env 7 /\program230_register actual 3=env 3 /\
 program230_register actual 4=env 0 /\program230_register actual 5=env 2 /\
 program230_register actual 6=zeroM M /\program230_register actual 7=zeroM M /\program230_register actual 8=env 10.
Proof.
 intro H;split.
 -apply(search_bundle_variables M env 0 2 3);exact(H 1 ltac:(lia)).
 -split.
  +apply(search_stack_variables M env 0 1 2 3 4 5 6);exact(H 2 ltac:(lia)).
  +split;[exact(H 0 ltac:(lia))|]. split;[exact(H 3 ltac:(lia))|]. split;[exact(H 4 ltac:(lia))|].
   split;[exact(H 5 ltac:(lia))|]. split;[exact(H 6 ltac:(lia))|]. split;[exact(H 7 ltac:(lia))|exact(H 8 ltac:(lia))].
Qed.
Theorem p230_ax_symbolic_result_graphs M env symbolic actual:
 p230_ax_symbolic_execute p230_ax_pre_gate_ids p230_ax_symbolic_initial=Some symbolic->
 p230_ax_register_graph M env symbolic actual->
 search_bundle M(env 0)(env 2)(env 3)(program230_register actual 1) /\
 search_stack M(env 0)(env 1)(env 2)(env 3)(env 4)(env 5)(env 6)(program230_register actual 2) /\
 program230_register actual 0=env 7 /\program230_register actual 3=env 3 /\
 program230_register actual 4=env 0 /\program230_register actual 5=env 2 /\
 program230_register actual 6=zeroM M /\program230_register actual 7=zeroM M /\program230_register actual 8=env 10.
Proof. rewrite p230_ax_symbolic_normalization;intro E;injection E as <-;apply p230_ax_symbolic_final_graphs. Qed.
Print Assumptions p230_ax_register_graph_total.
Print Assumptions p230_ax_symbolic_final_graphs.
Print Assumptions p230_ax_symbolic_result_graphs.
