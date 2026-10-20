(** The complete actual final AX gate, including selector cleanup and root return. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230PathCode Program230RootHistory Program230TransferEntry Program230RegisterLoops
 Program230TransferStates Program230Copy2States Program230Copy2Loop Program230AXGateSites
 Program230AXGateReload Program230AXGateFinish Program230ComparisonGuards Program230Selector
 Program230SelectorReturn Program230UnpairRestore.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Logic.Classical_Prop Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_gate_choices {D:Type}(a b c top out:D)z:
 (((c=a\/c=b)/\out=z)\/(c<>a/\c<>b/\out=top)) ->
 exists mid,((c=b/\mid=z)\/(c<>b/\mid=top)) /\((c=a/\out=z)\/(c<>a/\out=mid)).
Proof.
 intro H;destruct(classic(c=b))as[Hb|Hb];destruct(classic(c=a))as[Ha|Ha].
 -exists z;intuition congruence.
 -exists z;intuition congruence.
 -exists top;intuition congruence.
 -exists top;intuition congruence.
Qed.

Theorem p230_ax_gate_history M base a b c top out:
 (((c=a\/c=b)/\out=zeroM M)\/(c<>a/\c<>b/\out=top)) ->
 exists u v time,program230_history M p230_instruction_formula u v time
 (p230_ax_gate_state M base(program230_path_value M p230_ax_gate_copy)c a b top(zeroM M)(zeroM M)) /\
 program230_state_at M u v time(p230_ax_gate_state M base
 (program230_path_value M p230_selector_return_exit)(zeroM M)(zeroM M)(zeroM M)out(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time.
Proof.
 intro Hout;destruct(p230_gate_choices a b c top out(zeroM M)Hout)as[mid[Hmid Hlast]].
 set(start:=p230_ax_gate_state M base(program230_path_value M p230_ax_gate_copy)c a b top(zeroM M)(zeroM M)).
 destruct(p230_copy2_record M p230_ax_gate_copy 3 7 6 4947 4948 4949 start c
 ltac:(lia) ltac:(lia) ltac:(lia)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)p230_ax_gate_copy_site eq_refl eq_refl)
 as[u[v[Hcopy Hcopylast]]].
 assert(EC:program230_copy2_state 3 7 6 start(program230_path_value M(inc_path p230_ax_gate_copy))(zeroM M)
 (addM M(program230_register start 7)c)(addM M(program230_register start 6)c)=
 p230_ax_gate_state M base(program230_path_value M(inc_path p230_ax_gate_copy))(zeroM M)a b top c c).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
  change(program230_register
    (program230_copy2_state 3 7 6 start(program230_path_value M(inc_path p230_ax_gate_copy))(zeroM M)
     (addM M(program230_register start 7)c)(addM M(program230_register start 6)c))j=
   program230_register
    (p230_ax_gate_state M base(program230_path_value M(inc_path p230_ax_gate_copy))(zeroM M)a b top c c)j).
  rewrite program230_copy2_register by lia.
  do 9(destruct j as[|j];[try reflexivity;try(change(addM M(zeroM M)c=c);apply coding_add_zero)|]);lia. }
 rewrite EC in Hcopylast.
 destruct(p230_ax_gate_finish M base a b c top mid out Hmid Hlast)as[d[e[N[Q[HD[HE[HN HQ]]]]]]].
 assert(Hnz:N<>zeroM M)by(intro E;rewrite E in HN;destruct HN as[t Ht];rewrite coding_add_zero in Ht;exact(zero_ne_succ M t Ht)).
 assert(Hip:ipeq p230_comparison_parent_path_0(inc_path p230_ax_gate_copy)).
 {intro i;unfold p230_comparison_parent_path_0,p230_ax_gate_copy;do 32(destruct i;[reflexivity|]);reflexivity. }
 destruct(p230_history_ipeq_endpoint M d e N
 (p230_ax_gate_state M base(program230_path_value M p230_comparison_parent_path_0)(zeroM M)a b top c c)
 p230_comparison_parent_path_0(inc_path p230_ax_gate_copy)
 (p230_ax_gate_state M base(program230_path_value M Q)(zeroM M)(zeroM M)(zeroM M)out(zeroM M)(zeroM M))
 eq_refl Hip HD Hnz HE)as[f[g[HF[HG _]]]].
 change(program230_history M p230_instruction_formula f g N
 (p230_ax_gate_state M base(program230_path_value M(inc_path p230_ax_gate_copy))(zeroM M)a b top c c))in HF.
 destruct(program230_history_join M p230_instruction_formula u v(program230_copy2_time M c)f g N
 start _ Hcopy Hcopylast HF)as[h[i[HI[HL Hright]]]].
 pose proof(proj1(Hright N _(coding_lt_succ M N))HG)as Hgate.
 set(last:=p230_ax_gate_state M base(program230_path_value M Q)(zeroM M)(zeroM M)(zeroM M)out(zeroM M)(zeroM M))in *.
 destruct(p230_selector_ax_return M last)as[j[k[HJ HK]]].
 destruct(p230_history_ipeq_endpoint M j k(code_numeral M 3)
 (program230_with_pc last(program230_path_value M(inc_path p230_selector_ax)))
 (inc_path p230_selector_ax)Q
 (program230_with_pc last(program230_path_value M p230_selector_return_exit))
 eq_refl(ipeq_sym _ _ HQ)HJ
 ltac:(intro E;exact(zero_ne_succ M(code_numeral M 2)(eq_sym E)))HK)as[l[m[HL'[HM _]]]].
 rewrite program230_with_pc_twice,program230_with_pc_restore in HL' by reflexivity.
 destruct(program230_history_join M p230_instruction_formula h i(addM M(program230_copy2_time M c)N)
 l m(code_numeral M 3)start last HI Hgate HL')as[n[o[HO[HL'' Hright']]]].
 exists n,o,(addM M(addM M(program230_copy2_time M c)N)(code_numeral M 3));split;[exact HO|]. split.
 -exact(proj1(Hright' _ _(coding_lt_succ M _))HM).
 -apply program230_positive_sum;rewrite(Arithmetic.add_comm M);apply program230_positive_sum;exact HN.
Qed.
Print Assumptions p230_ax_gate_history.
