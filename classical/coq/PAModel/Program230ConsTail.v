(** The pair-and-fourfold-scale tail of cons119/wim. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230TransferStates Program230Copy2States
 Program230TransferProgram Program230InstructionFormula Program230SemanticHistories
 Program230StackStates Program230PairConstructorIteration Program230PairShape Program230PairEntry
 Program230Scale4Loop Program230Scale4Program Program230Scale4Entry.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma implication_pair_factor M a b out:implication_graph M a b out->
 exists p,pair_graph M a b p /\out=mulM M(code_numeral M 4)p.
Proof.
 unfold implication_graph;cbn[E_wim code_relation arguments2].
 intros[coefficient[p[Ec[[x[y[Hx[Hy Hpair]]]]E]]]];subst coefficient x y.
 exists p;exact(conj Hpair E).
Qed.
Definition program230_cons_tail_shape P:=program230_pair_shape(P++[true;false]) /\
 program230_scale4_leaves p230(P++[true;true])7 1.
Section Tail.
Variable M:Model.
Variable P:list bool.
Hypothesis Hshape:program230_cons_tail_shape P.
Local Notation Z:=(zeroM M).
Local Notation cfg:=program230_stack_state.
Theorem program230_cons_tail_history base x tw rest out:
 implication_graph M x tw out->exists u v time,
 program230_program_history M p230 u v time(cfg base(program230_path_value M(P++[true;false]))tw rest x Z) /\
 program230_state_at M u v time(cfg base(program230_path_value M(inc_path(P++[true;true])))out rest Z Z) /\
 coding_lt M Z time.
Proof.
 intro Hout;destruct(implication_pair_factor M x tw out Hout)as[p[Hpair Eout]].
 destruct Hshape as[HPair HScale].
 set(start:=cfg base(program230_path_value M(P++[true;false]))tw rest x Z).
 assert(HP:pair_graph M(program230_register start 6)(program230_register start 1)p).
 {unfold start;rewrite !program230_stack_register by lia;exact Hpair. }
 destruct(p230_pair_padded_entry M(P++[true;false])(P++[true;false])start p HPair eq_refl(ipeq_refl _)HP)
 as[a[b[N[HA[HTA HN]]]]].
 set(paired:=program230_pair_state start(program230_path_value M((inc_path(P++[true;false]))++[false]))Z Z
  (addM M(program230_register start 7)p))in *.
 assert(Epaired:paired=cfg base(program230_path_value M(P++[true;true;false]))Z rest Z p).
 {unfold paired;apply program230_stack_frame.
  -change(program230_path_value M((inc_path(P++[true;false]))++[false])=program230_path_value M(P++[true;true;false])).
   rewrite program230_pair_dec_path;f_equal;rewrite <-app_assoc;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;unfold start;rewrite program230_stack_register by lia;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -unfold program230_pair_state;rewrite program230_copy2_register by lia;unfold start;rewrite program230_stack_register by lia;apply coding_add_zero.
  -intros i Hi Hi1 Hi2 Hi6 Hi7;unfold program230_pair_state;rewrite program230_copy2_register by exact Hi.
   rewrite(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 7)Hi7).
   unfold start;rewrite program230_stack_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7). }
 rewrite Epaired in HTA.
 assert(Heq:ipeq(P++[true;true;false])(P++[true;true])).
 {replace(P++[true;true;false])with((P++[true;true])++[false])by(rewrite <-app_assoc;reflexivity);apply ipeq_app_false. }
 destruct(p230_scale4_padded_entry M(P++[true;true])(P++[true;true;false])7 1
 (cfg base(program230_path_value M(P++[true;true;false]))Z rest Z p)p
 ltac:(lia)ltac:(lia)ltac:(lia)HScale eq_refl Heq ltac:(rewrite program230_stack_register by lia;reflexivity))
 as[c[d[last[HC[HTC[Hpc[H7[H1 HF]]]]]]]].
 assert(Elast:last=cfg base(program230_path_value M(inc_path(P++[true;true])))out rest Z Z).
 {apply program230_stack_frame.
  -exact Hpc.
  -rewrite H1,program230_stack_register by lia;rewrite coding_add_zero;exact(eq_sym Eout).
  -rewrite(HF 2 ltac:(lia)ltac:(lia)ltac:(lia));rewrite program230_stack_register by lia;reflexivity.
  -rewrite(HF 6 ltac:(lia)ltac:(lia)ltac:(lia));rewrite program230_stack_register by lia;reflexivity.
  -exact H7.
  -intros i Hi Hi1 Hi2 Hi6 Hi7;rewrite(HF i Hi Hi7 Hi1),program230_stack_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7). }
 rewrite Elast in HTC.
 destruct(p230_program_history_join M a b N c d(program230_scale4_time M p)_ _ HA HTA HC)
 as[u[v[HR[HL HH]]]].
 exists u,v,(addM M N(program230_scale4_time M p));split;[exact HR|]. split.
 -exact(proj1(HH(program230_scale4_time M p)_(coding_lt_succ M(program230_scale4_time M p)))HTC).
 -apply program230_duration_add;apply program230_scale4_time_positive.
Qed.
End Tail.
Print Assumptions implication_pair_factor.
Print Assumptions program230_cons_tail_history.
