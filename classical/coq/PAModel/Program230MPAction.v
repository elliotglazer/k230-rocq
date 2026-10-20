(** Complete literal MP action, with both equality outcomes and genuine histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferProgram
 Program230InstructionFormula Program230RootHistory Program230RootReady Program230SemanticHistories
 Program230TransferEntry Program230StackStates Program230UnpairRestore Program230Selector
 Program230ComparisonIteration Program230ComparisonControl Program230ComparisonGuards
 Program230MPTransport Program230MPTest Program230MPSuccessParameter.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_mp_success_exit:=inc_path(p230_mp_success_parameter_path++[true]).
Definition p230_mp_action_output M base tw ws b c time exit newtw newws:=
 program230_program_history M p230 b c time
 (program230_stack_state base(program230_path_value M p230_selector_mp)tw ws(zeroM M)(zeroM M)) /\
 program230_state_at M b c time(p230_mp_output_state M base(program230_path_value M exit)newtw newws) /\
 coding_lt M(zeroM M)time.
Theorem p230_mp_action_equal M base tw ws value saved:
 implication_graph M tw(program230_register base 4)value->value=program230_register base 5->
 pair_graph M(zeroM M)ws saved->exists b c time,
 p230_mp_action_output M base tw ws b c time p230_mp_success_exit(program230_register base 4)saved.
Proof.
 intros HV HE HS.
 destruct(proj1(p230_mp_test_histories M base tw ws value HV)HE)as[a[b[N[HA[HTA HN]]]]].
 set(cleared:=program230_comparison_state base(program230_path_value M p230_mp_equal_exit)(zeroM M)(zeroM M)).
 destruct(p230_mp_success_parameter_history M cleared(zeroM M)ws saved HS)
 as[c[d[K[HC[HTC HK]]]]].
 assert(Hpad:ipeq p230_mp_success_push_path p230_mp_equal_exit).
 {unfold p230_mp_success_push_path,p230_mp_equal_exit,p230_comparison_parent_path_3;vm_compute;unfold ipeq,bit;intro i;
 do 12(destruct i as[|i];[reflexivity|]);reflexivity. }
 destruct(p230_positive_history_entry M p230_mp_success_push_path p230_mp_equal_exit
 (program230_stack_state cleared(program230_path_value M p230_mp_success_push_path)(zeroM M)ws(zeroM M)(zeroM M))_
 c d K eq_refl Hpad HC HTC HK)as[e[f[HEF HTF]]].
 rewrite program230_stack_with_pc in HEF.
 destruct(p230_program_history_join M a b N e f K _ _ HA HTA HEF)as[u[v[HU[HL HH]]]].
 exists u,v,(addM M N K);unfold p230_mp_action_output;split;[exact HU|]. split.
 -pose proof(proj1(HH K _(coding_lt_succ M K))HTF)as HT.
  assert(E:program230_stack_state cleared(program230_path_value M p230_mp_success_exit)
   (program230_register cleared 4)saved(zeroM M)(zeroM M)=
   p230_mp_output_state M base(program230_path_value M p230_mp_success_exit)(program230_register base 4)saved).
  {unfold cleared,p230_mp_output_state;destruct base;reflexivity. }
  rewrite <-E;exact HT.
 -apply program230_positive_sum;exact HN.
Qed.
Theorem p230_mp_action_unequal M base tw ws value:
 implication_graph M tw(program230_register base 4)value->value<>program230_register base 5->
 exists b c time,p230_mp_action_output M base tw ws b c time p230_mp_unequal_exit(zeroM M)ws.
Proof. intros HV HE;exact(proj2(p230_mp_test_histories M base tw ws value HV)HE). Qed.
Theorem p230_mp_action_total M base tw ws:
 exists value saved,implication_graph M tw(program230_register base 4)value /\
 pair_graph M(zeroM M)ws saved /\
 (value=program230_register base 5->exists b c time,
  p230_mp_action_output M base tw ws b c time p230_mp_success_exit(program230_register base 4)saved) /\
 (value<>program230_register base 5->exists b c time,
  p230_mp_action_output M base tw ws b c time p230_mp_unequal_exit(zeroM M)ws).
Proof.
 destruct(code_relation_total M(E_wim(CEvar 0)(CEvar 1))(arguments2 tw(program230_register base 4)(zeroM M)))as[value HV].
 destruct(pair_total M(zeroM M)ws)as[saved HS].
 exists value,saved;split;[exact HV|]. split;[exact HS|]. split.
 -intro HE;exact(p230_mp_action_equal M base tw ws value saved HV HE HS).
 -intro HE;exact(p230_mp_action_unequal M base tw ws value HV HE).
Qed.
Lemma p230_mp_return_paths:
 p230_mp_success_exit=repeat false 8 /\p230_mp_unequal_exit=repeat false 5.
Proof. split;reflexivity. Qed.
Theorem p230_mp_return_ready M:
 program230_root_ready M(program230_path_value M p230_mp_success_exit) /\
 program230_root_ready M(program230_path_value M p230_mp_unequal_exit).
Proof. destruct p230_mp_return_paths as[HS HF];rewrite HS,HF;split;[exists 8|exists 5];split;[lia|reflexivity|lia|reflexivity]. Qed.
Lemma p230_mp_output_fields M base pc tw ws:
 program230_pc(p230_mp_output_state M base pc tw ws)=pc /\
 program230_register(p230_mp_output_state M base pc tw ws)1=tw /\
 program230_register(p230_mp_output_state M base pc tw ws)2=ws /\
 program230_register(p230_mp_output_state M base pc tw ws)5=zeroM M /\
 program230_register(p230_mp_output_state M base pc tw ws)6=zeroM M /\
 program230_register(p230_mp_output_state M base pc tw ws)7=zeroM M /\
 (forall i,(i<9)%nat->i<>1->i<>2->i<>5->i<>6->i<>7->
  program230_register(p230_mp_output_state M base pc tw ws)i=program230_register base i).
Proof.
 repeat split;try reflexivity.
 intros i Hi Hi1 Hi2 Hi5 Hi6 Hi7;unfold p230_mp_output_state.
 rewrite program230_stack_register by exact Hi.
 rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7).
 rewrite comparison_register by exact Hi.
 now rewrite(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 5)Hi5).
Qed.
Print Assumptions p230_mp_action_equal.
Print Assumptions p230_mp_action_unequal.
Print Assumptions p230_mp_action_total.
Print Assumptions p230_mp_return_ready.
Print Assumptions p230_mp_output_fields.
