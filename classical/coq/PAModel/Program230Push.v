(** Complete stack push from actual finite p230 pieces. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230TransferStates Program230Copy2States Program230TransferProgram
 Program230TransferLoop Program230InstructionFormula Program230SemanticHistories
 Program230TransferEntry Program230StackStates Program230PairConstructorIteration Program230PairShape
 Program230PairEntry Program230PushParts.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Push.
Variable M:Model.
Variable P:list bool.
Hypothesis Hshape:program230_push_shape P.
Local Notation Z:=(zeroM M).
Local Notation cfg:=program230_stack_state.
Lemma program230_push_pair base tw ws value:
 pair_graph M tw ws value->exists u v time,
 program230_program_history M p230 u v time(cfg base(program230_path_value M(P++[true;true]))ws Z tw Z) /\
 program230_state_at M u v time(cfg base(program230_path_value M(P++[true;true;true;false]))Z Z Z value) /\
 coding_lt M Z time.
Proof.
 intro Hpair;pose proof(proj1(proj2(proj2 Hshape)))as HS.
 set(start:=cfg base(program230_path_value M(P++[true;true]))ws Z tw Z).
 assert(Heq:ipeq(P++[true;true])(P++[true;true;false])).
 {replace(P++[true;true;false])with((P++[true;true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply ipeq_sym,ipeq_app_false. }
 assert(Hpair':pair_graph M(program230_register start 6)(program230_register start 1)value).
 {unfold start;rewrite !program230_stack_register by lia;exact Hpair. }
 destruct(p230_pair_padded_entry M(P++[true;true;false])(P++[true;true])start value HS eq_refl Heq Hpair')
 as[u[v[time[HR[HT Hpos]]]]].
 set(final:=program230_pair_state start
  (program230_path_value M((inc_path(P++[true;true;false]))++[false]))Z Z
  (addM M(program230_register start 7)value))in *.
 assert(E:final=cfg base(program230_path_value M(P++[true;true;true;false]))Z Z Z value).
 {unfold final;apply program230_stack_frame.
  -change(program230_path_value M((inc_path(P++[true;true;false]))++[false])=program230_path_value M(P++[true;true;true;false]));f_equal.
   replace(P++[true;true;false])with((P++[true;true])++[false])by(rewrite <-app_assoc;reflexivity).
   rewrite inc_path_app_false;repeat rewrite <-app_assoc;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;unfold start;rewrite program230_stack_register by lia;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;unfold start;rewrite program230_stack_register by lia;apply coding_add_zero.
  -intros i Hi Hi1 Hi2 Hi6 Hi7;unfold program230_pair_state;rewrite program230_copy2_register by exact Hi.
   rewrite(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 7)Hi7).
   unfold start;rewrite program230_stack_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7). }
 exists u,v,time;split;[exact HR|]. split;[now rewrite <-E|exact Hpos].
Qed.
Theorem program230_push_history base tw ws value:
 pair_graph M tw ws value->exists u v time,
 program230_program_history M p230 u v time(cfg base(program230_path_value M P)tw ws Z Z) /\
 program230_state_at M u v time(cfg base(program230_path_value M(inc_path(P++[true;true;true])))Z value Z Z) /\
 coding_lt M Z time.
Proof.
 intro Hpair.
 destruct(program230_push_first M P Hshape base tw ws)as[a[b[s1[H1[HT1 E1]]]]];subst s1.
 destruct(program230_push_second M P Hshape base tw ws)as[c[d[s2[H2[HT2 E2]]]]];subst s2.
 destruct(p230_program_history_join M a b(program230_transfer_time M tw)c d(program230_transfer_time M ws)_ _ H1 HT1 H2)
 as[e[f[H12[HL12 HR12]]]].
 pose proof(proj1(HR12(program230_transfer_time M ws)_(coding_lt_succ M(program230_transfer_time M ws)))HT2)as HT12.
 destruct(program230_push_pair base tw ws value Hpair)as[g[h[N[H3[HT3 HN]]]]].
 destruct(p230_program_history_join M e f(addM M(program230_transfer_time M tw)(program230_transfer_time M ws))g h N _ _ H12 HT12 H3)
 as[i[j[H123[HL123 HR123]]]].
 pose proof(proj1(HR123 N _(coding_lt_succ M N))HT3)as HT123.
 destruct(program230_push_last M P Hshape base value)as[k[l[s4[H4[HT4 E4]]]]];subst s4.
 destruct(p230_program_history_join M i j(addM M(addM M(program230_transfer_time M tw)(program230_transfer_time M ws))N)
 k l(program230_transfer_time M value)_ _ H123 HT123 H4)as[u[v[HR[HL HH]]]].
 exists u,v,(addM M(addM M(addM M(program230_transfer_time M tw)(program230_transfer_time M ws))N)(program230_transfer_time M value)).
 split;[exact HR|]. split.
 -exact(proj1(HH(program230_transfer_time M value)_(coding_lt_succ M(program230_transfer_time M value)))HT4).
 -apply program230_duration_add;apply program230_transfer_time_positive.
Qed.
End Push.
Print Assumptions program230_push_pair.
Print Assumptions program230_push_history.
