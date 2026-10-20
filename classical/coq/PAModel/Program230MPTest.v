(** Actual equality outcomes after the literal MP constructor prefix. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferProgram
 Program230InstructionFormula Program230SemanticHistories Program230StackStates
 Program230UnpairRestore Program230Selector Program230ComparisonIteration Program230ComparisonControl
 Program230ComparisonGuards Program230EqualitySites Program230MPTransport Program230MPPrefix.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_mp_output_state M base pc tw ws:=
 program230_stack_state(program230_comparison_state base pc(zeroM M)(zeroM M))pc tw ws(zeroM M)(zeroM M).
Definition p230_mp_equal_exit:=inc_path p230_comparison_parent_path_3++[false].
Definition p230_mp_unequal_exit:=brk 1 p230_comparison_parent_path_3.
Definition p230_mp_test_output M base tw ws time b c exit:=
 program230_program_history M p230 b c time
  (program230_stack_state base(program230_path_value M p230_selector_mp)tw ws(zeroM M)(zeroM M)) /\
 program230_state_at M b c time
  (p230_mp_output_state M base(program230_path_value M exit)(zeroM M)ws) /\
 coding_lt M(zeroM M)time.
Theorem p230_mp_test_histories M base tw ws value:
 implication_graph M tw(program230_register base 4)value->
 (value=program230_register base 5->exists b c time,p230_mp_test_output M base tw ws time b c p230_mp_equal_exit) /\
 (value<>program230_register base 5->exists b c time,p230_mp_test_output M base tw ws time b c p230_mp_unequal_exit).
Proof.
 intro Hv;destruct(pair_total M tw ws)as[pushed Hp].
 destruct(p230_mp_prefix_history M base tw ws pushed value Hp Hv)as[b[c[N[HR[HT HN]]]]].
 rewrite p230_mp_comparison_start in HT.
 set(testbase:=program230_stack_state base(program230_path_value M p230_comparison_parent_path_3)(zeroM M)ws(zeroM M)(zeroM M))in *.
 pose proof(p230_equality_site_histories M p230_comparison_parent_path_3 testbase value(program230_register base 5)equality_site_3)as[HE HNE].
 split;intro H.
 -destruct(HE H)as[d[e[K[HD[HTD HK]]]]].
  apply(proj1(p230_instruction_history_correct M d e K _))in HD.
  destruct(p230_program_history_join M b c N d e K _ _ HR HT HD)as[f[g[HF[HL HH]]]].
  exists f,g,(addM M N K);unfold p230_mp_test_output;split;[exact HF|]. split.
  +pose proof(proj1(HH K _(coding_lt_succ M K))HTD)as Hlast.
    unfold testbase in Hlast;rewrite p230_mp_comparison_end in Hlast;exact Hlast.
  +apply program230_positive_sum;exact HN.
 -destruct(HNE H)as[d[e[K[HD[HTD HK]]]]].
  apply(proj1(p230_instruction_history_correct M d e K _))in HD.
  destruct(p230_program_history_join M b c N d e K _ _ HR HT HD)as[f[g[HF[HL HH]]]].
  exists f,g,(addM M N K);unfold p230_mp_test_output;split;[exact HF|]. split.
  +pose proof(proj1(HH K _(coding_lt_succ M K))HTD)as Hlast.
    unfold testbase in Hlast;rewrite p230_mp_comparison_end in Hlast;exact Hlast.
  +apply program230_positive_sum;exact HN.
Qed.
Print Assumptions p230_mp_test_histories.
