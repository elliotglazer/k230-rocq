(** Actual first cons119/wim occurrence of the public program. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferStates Program230TransferProgram
 Program230InstructionFormula Program230RootHistory Program230SemanticHistories Program230TransferEntry
 Program230StackStates Program230PairConstructorIteration Program230PairShape Program230ConsTail
 Program230Copy2Program Program230Scale4Program Program230UnpairRestore Program230UnpairSites.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_cons_shape P:=exists un n m,
 In(P++[false;false],2,un)p230_unpair_sites /\
 program230_transfer_occurrence p230(P++[false;true])7 2 n m /\
 program230_cons_tail_shape P.
Theorem program230_cons_history M P base tw stack x rest out:
 program230_cons_shape P->pair_graph M x rest stack->implication_graph M x tw out->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M P)tw stack(zeroM M)(zeroM M)) /\
 program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(P++[true;true])))out rest(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time.
Proof.
 intros[un[n[m[Hun[Htransfer Htail]]]]]Hstack Hout.
 set(start:=program230_stack_state base(program230_path_value M P)tw stack(zeroM M)(zeroM M)).
 set(canonical:=program230_with_pc start(program230_path_value M (P++[false]))).
 assert(Hpair:pair_graph M x rest(program230_register canonical 2)).
 {unfold canonical;rewrite program230_with_pc_register;unfold start;rewrite program230_stack_register by lia;exact Hstack. }
 assert(H6:program230_register canonical 6=zeroM M).
 {unfold canonical;rewrite program230_with_pc_register;unfold start;rewrite program230_stack_register by lia;reflexivity. }
 assert(H7:program230_register canonical 7=zeroM M).
 {unfold canonical;rewrite program230_with_pc_register;unfold start;rewrite program230_stack_register by lia;reflexivity. }
 assert(Hun':In((P++[false])++[false],2,un)p230_unpair_sites)by(now rewrite <-app_assoc).
 assert(Htr':program230_transfer_occurrence p230((P++[false])++[true])7 2 n m)by(now rewrite <-app_assoc).
 destruct(p230_unpair_restore M(P++[false])2 un n m canonical x rest Hun' Htr' eq_refl Hpair H6 H7)
 as[a[b[N[mid[HA[HTA[HN[Hpc[Hx[Hz[Hr HF]]]]]]]]]]].
 apply(proj2(p230_instruction_history_correct M a b N canonical))in HA.
 assert(HN0:N<>zeroM M).
 {intro E;rewrite E in HN;destruct HN as[d Hd];rewrite coding_add_zero in Hd;exact(zero_ne_succ M d Hd). }
 assert(Heq:ipeq (P++[false]) P)by apply ipeq_app_false.
 destruct(p230_history_ipeq_endpoint M a b N canonical (P++[false]) P mid eq_refl Heq HA HN0 HTA)
 as[c[d[HC[HTC _]]]].
 assert(EC:program230_with_pc canonical(program230_path_value M P)=start).
 {unfold canonical;rewrite program230_with_pc_twice;apply program230_with_pc_restore;reflexivity. }
 rewrite EC in HC;apply(proj1(p230_instruction_history_correct M c d N start))in HC.
 assert(Emid:mid=program230_stack_state base(program230_path_value M(P++[true;false]))tw rest x(zeroM M)).
 {apply program230_stack_frame.
  -rewrite Hpc,inc_path_app_false;f_equal;rewrite <-app_assoc;reflexivity.
  -rewrite(HF 1 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));unfold canonical;rewrite program230_with_pc_register;unfold start;rewrite program230_stack_register by lia;reflexivity.
  -exact Hr.
  -exact Hx.
  -exact Hz.
  -intros i Hi Hi1 Hi2 Hi6 Hi7;rewrite(HF i Hi Hi2 Hi6 Hi7);unfold canonical;rewrite program230_with_pc_register;unfold start;rewrite program230_stack_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7). }
 rewrite Emid in HTC.
 destruct(program230_cons_tail_history M P Htail base x tw rest out Hout)
 as[e[f[K[HE[HTE HK]]]]].
 destruct(p230_program_history_join M c d N e f K start _ HC HTC HE)as[u[v[HR[HL HH]]]].
 exists u,v,(addM M N K);split;[exact HR|]. split.
 -exact(proj1(HH K _(coding_lt_succ M K))HTE).
 -apply program230_duration_add;exact HK.
Qed.
Print Assumptions program230_cons_history.
