(** Real push and implication histories preserve the AX code graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230InstructionFormula Program230PathCode
 Program230TransferStates Program230StackStates Program230PushSites Program230ConsSites
 Program230AXSymbolic Program230AXSymbolicGraphs Program230AXGraphEffects Program230AXRuntimeInterface.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_ax_stack_initial M start P:
 program230_pc start=program230_path_value M P ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 program230_stack_state start(program230_path_value M P)(program230_register start 1)
 (program230_register start 2)(zeroM M)(zeroM M)=start.
Proof. intros HP H6 H7;symmetry;apply program230_stack_frame;try assumption;reflexivity. Qed.
Lemma p230_ax_stack_updates M start pc top stack:
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 program230_stack_state start pc top stack(zeroM M)(zeroM M)=
 p230_ax_actual_set M(p230_ax_actual_set M start 1 top pc)2 stack pc.
Proof.
 intros H6 H7;apply p230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
 change(program230_register(program230_stack_state start pc top stack(zeroM M)(zeroM M))j=
 program230_register(p230_ax_actual_set M(p230_ax_actual_set M start 1 top pc)2 stack pc)j).
 rewrite program230_stack_register,!p230_ax_actual_set_register by lia.
 do 9(destruct j as[|j];[cbn[Nat.eqb];try reflexivity;try symmetry;assumption|]);lia.
Qed.
Lemma p230_ax_runtime_push M env symbolic start P:
 p230_push_site P ->program230_pc start=program230_path_value M P ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 p230_ax_register_graph M env symbolic start ->
 p230_ax_runtime_result M env(p230_ax_push symbolic(CEconst 0))start(inc_path(P++[true;true;true])).
Proof.
 intros HS HP H6 H7 HG.
 destruct(pair_total M(program230_register start 1)(program230_register start 2))as[word HW].
 destruct(p230_push_site_history M P start _ _ word HS HW)as[b[c[time[HR[HT Hpos]]]]].
 rewrite(p230_ax_stack_initial M start P HP H6 H7)in HR.
 exists b,c,time,(program230_stack_state start(program230_path_value M(inc_path(P++[true;true;true])))
 (zeroM M)word(zeroM M)(zeroM M));split.
 -apply(proj2(p230_instruction_history_correct M b c time start));exact HR.
 -split;[exact HT|split;[exact Hpos|split;[reflexivity|]]].
  rewrite(p230_ax_stack_updates M start _ _ _ H6 H7).
  assert(E:p230_ax_actual_set M(p230_ax_actual_set M start 1(zeroM M)(program230_path_value M(inc_path(P++[true;true;true]))))2 word(program230_path_value M(inc_path(P++[true;true;true])))=
  p230_ax_actual_set M(p230_ax_actual_set M start 2 word(program230_path_value M(inc_path(P++[true;true;true]))))1(zeroM M)(program230_path_value M(inc_path(P++[true;true;true])))).
  {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
   do 9(destruct j as[|j];[reflexivity|]);lia. }
  rewrite E;apply p230_ax_graph_push;assumption.
Qed.
Lemma p230_ax_runtime_cons M env symbolic start site x tail:
 In site p230_cons_sites ->program230_pc start=program230_path_value M(cons_path site) ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 p230_ax_register_graph M env symbolic start ->program230_register symbolic 2=CEpair x tail ->
 p230_ax_runtime_result M env
 (p230_ax_set(p230_ax_set symbolic 1(E_wim x(program230_register symbolic 1)))2 tail)
 start(inc_path(cons_path site++[true;true])).
Proof.
 intros HS HP H6 H7 HG Hshape.
 pose proof(HG 2 ltac:(lia))as Hstack;rewrite Hshape in Hstack.
 destruct Hstack as[value[rest[HX[HTail Hpair]]]].
 destruct(code_relation_total M(E_wim(CEvar 0)(CEvar 1))
 (arguments2 value(program230_register start 1)(zeroM M)))as[out Hout].
 change(implication_graph M value(program230_register start 1)out)in Hout.
 destruct(p230_cons_site_history M site start _ _ value rest out HS Hpair Hout)
 as[b[c[time[HR[HT Hpos]]]]].
 rewrite(p230_ax_stack_initial M start(cons_path site)HP H6 H7)in HR.
 exists b,c,time,(program230_stack_state start(program230_path_value M(inc_path(cons_path site++[true;true])))out rest(zeroM M)(zeroM M));split.
 -apply(proj2(p230_instruction_history_correct M b c time start));exact HR.
 -split;[exact HT|split;[exact Hpos|split;[reflexivity|]]].
  rewrite(p230_ax_stack_updates M start _ _ _ H6 H7).
  apply(p230_ax_graph_cons M env symbolic start x tail value rest out _ HG Hshape HX HTail Hout).
Qed.
Print Assumptions p230_ax_runtime_push.
Print Assumptions p230_ax_runtime_cons.
