(** Exact first push-and-load-parameter sequence, with all PC padding retained. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230Histories Program230TransferStates Program230TransferProgram
 Program230InstructionFormula Program230RootHistory Program230SemanticHistories
 Program230TransferEntry Program230StackStates Program230PushParts Program230Push Program230ParameterLoad
 Program230PairConstructorIteration.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem program230_parameter_push_history M P Q r base tw ws value:
 (r<9)%nat->r<>1->r<>2->r<>6->r<>7->
 program230_push_shape P->program230_parameter_shape Q r->
 ipeq Q(inc_path(P++[true;true;true]))->pair_graph M tw ws value->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M P)tw ws(zeroM M)(zeroM M)) /\
 program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(Q++[true])))
   (program230_register base r)value(zeroM M)(zeroM M)) /\coding_lt M(zeroM M)time.
Proof.
 intros Hr Hr1 Hr2 Hr6 Hr7 Hpush Hparam Hconnect Hpair.
 destruct(program230_push_history M P Hpush base tw ws value Hpair)as[a[b[N[HA[HTA HN]]]]].
 set(pushed:=program230_stack_state base
  (program230_path_value M(inc_path(P++[true;true;true])))
  (zeroM M)value(zeroM M)(zeroM M))in *.
 set(canonical:=program230_with_pc pushed(program230_path_value M Q)).
 assert(H1:program230_register canonical 1=zeroM M).
 {unfold canonical;rewrite program230_with_pc_register;unfold pushed;rewrite program230_stack_register by lia;reflexivity. }
 assert(H6:program230_register canonical 6=zeroM M).
 {unfold canonical;rewrite program230_with_pc_register;unfold pushed;rewrite program230_stack_register by lia;reflexivity. }
 destruct(program230_parameter_history M Q r canonical Hr Hr1 Hr6 Hparam eq_refl H1 H6)as[c[d[K[last[HC[HTC[HK[Hpc[Htw[Hz HF]]]]]]]]]].
 apply(proj2(p230_instruction_history_correct M c d K canonical))in HC.
 assert(HK0:K<>zeroM M).
 {intro E;rewrite E in HK;destruct HK as[x Hx];rewrite coding_add_zero in Hx;exact(zero_ne_succ M x Hx). }
 destruct(p230_history_ipeq_endpoint M c d K canonical Q
 (inc_path(P++[true;true;true]))last eq_refl Hconnect HC HK0 HTC)
 as[e[f[HE[HTE _]]]].
 assert(E:program230_with_pc canonical(program230_path_value M(inc_path(P++[true;true;true])))=pushed).
 {unfold canonical;rewrite program230_with_pc_twice;apply program230_with_pc_restore;reflexivity. }
 rewrite E in HE;apply(proj1(p230_instruction_history_correct M e f K pushed))in HE.
 destruct(p230_program_history_join M a b N e f K _ pushed HA HTA HE)as[u[v[HR[HL HH]]]].
 assert(Elast:last=program230_stack_state base(program230_path_value M(inc_path(Q++[true])))
  (program230_register base r)value(zeroM M)(zeroM M)).
 {apply program230_stack_frame.
  -exact Hpc.
  -rewrite Htw;unfold canonical;rewrite program230_with_pc_register;unfold pushed;rewrite program230_stack_register by exact Hr.
   now rewrite(proj2(Nat.eqb_neq r 1)Hr1),(proj2(Nat.eqb_neq r 2)Hr2),(proj2(Nat.eqb_neq r 6)Hr6),(proj2(Nat.eqb_neq r 7)Hr7).
  -rewrite(HF 2 ltac:(lia)ltac:(lia)ltac:(lia));unfold canonical;rewrite program230_with_pc_register;unfold pushed;rewrite program230_stack_register by lia;reflexivity.
  -exact Hz.
  -rewrite(HF 7 ltac:(lia)ltac:(lia)ltac:(lia));unfold canonical;rewrite program230_with_pc_register;unfold pushed;rewrite program230_stack_register by lia;reflexivity.
  -intros i Hi Hi1 Hi2 Hi6 Hi7;rewrite(HF i Hi Hi1 Hi6);unfold canonical;rewrite program230_with_pc_register;unfold pushed;rewrite program230_stack_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7). }
 exists u,v,(addM M N K);split;[exact HR|]. split.
 -rewrite <-Elast;exact(proj1(HH K _(coding_lt_succ M K))HTE).
 -apply program230_duration_add;exact HK.
Qed.
Print Assumptions program230_parameter_push_history.
