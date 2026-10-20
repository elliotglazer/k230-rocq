(** Actual two-comparison AX gate after copying the selector into both scratches. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230PathCode Program230AXGateSites Program230AXGateReload Program230AXGateTest
 Program230AXZeroTest Program230EqualitySites Program230ComparisonGuards Program230Selector
 Program230UnpairRestore Program230TransferLoop.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_ax_gate_finish M base a b c top mid out:
 ((c=b /\mid=zeroM M)\/(c<>b /\mid=top)) ->
 ((c=a /\out=zeroM M)\/(c<>a /\out=mid)) ->
 exists u v time Q,program230_history M p230_instruction_formula u v time
  (p230_ax_gate_state M base(program230_path_value M p230_comparison_parent_path_0)
    (zeroM M)a b top c c) /\
 program230_state_at M u v time(p230_ax_gate_state M base(program230_path_value M Q)
    (zeroM M)(zeroM M)(zeroM M)out(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time /\ipeq Q(inc_path p230_selector_ax).
Proof.
 intros Hfirst Hsecond.
 set(start:=p230_ax_gate_state M base(program230_path_value M p230_comparison_parent_path_0)
    (zeroM M)a b top c c).
 destruct(p230_ax_zero_test M p230_comparison_parent_path_0 4963 start top c b mid
  equality_site_0 p230_ax_gate_reset0_site Hfirst)as[u[v[N[Q[H1[H1last[HN HQ]]]]]]].
 change(program230_history M p230_instruction_formula u v N start)in H1.
 change(program230_state_at M u v N(p230_ax_gate_state M base(program230_path_value M Q)
   (zeroM M)a(zeroM M)mid(zeroM M)c))in H1last.
 assert(HQrestore:ipeq Q p230_ax_gate_restore).
 {destruct HQ as[[_ ->]|[_ ->]];intro i;unfold p230_comparison_parent_path_0,p230_ax_gate_restore,p230_ax_gate_path;
  do 32(destruct i;[reflexivity|]);reflexivity. }
 destruct(p230_ax_gate_reload M base a c mid Q HQrestore)as[d[e[H2 H2last]]].
 set(second:=p230_ax_gate_state M base(program230_path_value M(p230_comparison_parent_path_1++[false]))
   (zeroM M)(zeroM M)a mid c(zeroM M))in *.
 destruct(p230_ax_zero_test_padded M p230_comparison_parent_path_1
  (p230_comparison_parent_path_1++[false])4980 second mid c a out
  equality_site_1 p230_ax_gate_reset1_site(ipeq_app_false _)Hsecond)
 as[f[g[K[R[H3[H3last[HK HR]]]]]]].
 change(program230_history M p230_instruction_formula f g K second)in H3.
 change(program230_state_at M f g K(p230_ax_gate_state M base(program230_path_value M R)
   (zeroM M)(zeroM M)(zeroM M)out(zeroM M)(zeroM M)))in H3last.
 assert(HRfinal:ipeq R(inc_path p230_selector_ax)).
 {destruct HR as[[_ ->]|[_ ->]];intro i;unfold p230_comparison_parent_path_1,p230_selector_ax;
  do 32(destruct i;[reflexivity|]);reflexivity. }
 destruct(program230_history_join M p230_instruction_formula u v N d e
  (addM M(program230_transfer_time M c)(program230_transfer_time M a))start _ H1 H1last H2)
 as[h[j[H12[HL Hright]]]].
 pose proof(proj1(Hright _ _(coding_lt_succ M _))H2last)as Hsecondlast.
 destruct(program230_history_join M p230_instruction_formula h j
  (addM M N(addM M(program230_transfer_time M c)(program230_transfer_time M a)))f g K
  start second H12 Hsecondlast H3)as[k[l[H123[HL' Hright']]]].
 exists k,l,(addM M(addM M N(addM M(program230_transfer_time M c)(program230_transfer_time M a)))K),R.
 split;[exact H123|]. split;[exact(proj1(Hright' _ _(coding_lt_succ M _))H3last)|].
 split;[apply program230_positive_sum;apply program230_positive_sum;exact HN|exact HRfinal].
Qed.
Print Assumptions p230_ax_gate_finish.
