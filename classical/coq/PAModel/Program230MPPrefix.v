(** The literal MP prefix constructs the implication and moves it into the test register. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferProgram
 Program230TransferLoop Program230InstructionFormula Program230RootHistory Program230SemanticHistories Program230TransferEntry
 Program230StackStates Program230MPParameterCore Program230MPCons Program230MPTransport
 Program230UnpairRestore Program230Selector Program230ComparisonIteration Program230ComparisonControl
 Program230ComparisonGuards.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_mp_transfer_path:list bool:=[true;true;true;true;false;true].
Lemma p230_mp_transfer_occurrence:program230_transfer_occurrence p230 p230_mp_transfer_path 1 6 5086 5087.
Proof. unfold program230_transfer_occurrence;vm_compute;repeat split;reflexivity. Qed.
Theorem p230_mp_prefix_history M base tw ws pushed value:
 pair_graph M tw ws pushed->implication_graph M tw(program230_register base 4)value->
 exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M p230_selector_mp)tw ws(zeroM M)(zeroM M)) /\
 program230_state_at M u v time
  (program230_stack_state base(program230_path_value M p230_comparison_parent_path_3)(zeroM M)ws value(zeroM M)) /\
 coding_lt M(zeroM M)time.
Proof.
 intros Hp Hv.
 destruct(p230_mp_core_parameter_history M base tw ws pushed Hp)as[a[b[N[HA[HTA HN]]]]].
 assert(Hpad:ipeq p230_mp_core_push_path p230_selector_mp).
 {unfold p230_mp_core_push_path,p230_selector_mp;unfold ipeq,bit;intro i;do 10(destruct i as[|i];[reflexivity|]);reflexivity. }
 destruct(p230_positive_history_entry M p230_mp_core_push_path p230_selector_mp (program230_stack_state base(program230_path_value M p230_mp_core_push_path)tw ws(zeroM M)(zeroM M)) _ a b N eq_refl Hpad HA HTA HN)
 as[c[d[HC HTC]]]. rewrite program230_stack_with_pc in HC.
 destruct(p230_mp_cons_history M base(program230_register base 4)pushed tw ws value Hp Hv)
 as[e[f[K[HE[HTE HK]]]]].
 assert(Hpad2:ipeq p230_mp_cons_path(inc_path(p230_mp_core_parameter_path++[true]))).
 {unfold p230_mp_cons_path,p230_mp_core_parameter_path;vm_compute;unfold ipeq,bit;intro i;do 12(destruct i as[|i];[reflexivity|]);reflexivity. }
 destruct(p230_positive_history_entry M p230_mp_cons_path(inc_path(p230_mp_core_parameter_path++[true])) (program230_stack_state base(program230_path_value M p230_mp_cons_path)(program230_register base 4)pushed(zeroM M)(zeroM M)) _ e f K eq_refl Hpad2 HE HTE HK)
 as[g[h[HG HTH]]]. rewrite program230_stack_with_pc in HG.
 destruct(p230_program_history_join M c d N g h K _ _ HC HTC HG)as[j[k[HJ[HL HH]]]].
 pose proof(proj1(HH K _(coding_lt_succ M K))HTH)as HTJ.
 set(mid:=program230_stack_state base(program230_path_value M(inc_path(p230_mp_cons_path++[true;true])))value ws(zeroM M)(zeroM M))in *.
 assert(Hpad3:ipeq(inc_path(p230_mp_cons_path++[true;true]))p230_mp_transfer_path).
 {unfold p230_mp_cons_path,p230_mp_transfer_path;vm_compute;unfold ipeq,bit;intro i;do 12(destruct i as[|i];[reflexivity|]);reflexivity. }
 assert(Hcount:program230_register mid 1=value).
 {unfold mid;rewrite program230_stack_register by lia;reflexivity. }
 destruct(p230_transfer_padded_entry M p230_mp_transfer_path(inc_path(p230_mp_cons_path++[true;true]))1 6 5086 5087 mid value
 ltac:(lia)ltac:(lia)ltac:(lia)p230_mp_transfer_occurrence eq_refl Hpad3 Hcount)
 as[l[m[last[HM[HTM[Hpc[H1[H6 HF]]]]]]]].
 assert(EL:last=program230_stack_state base(program230_path_value M p230_comparison_parent_path_3)(zeroM M)ws value(zeroM M)).
 {apply program230_stack_frame.
  -exact Hpc.
  -exact H1.
  -rewrite(HF 2 ltac:(lia)ltac:(lia)ltac:(lia));unfold mid;rewrite program230_stack_register by lia;reflexivity.
  -rewrite H6;unfold mid;rewrite program230_stack_register by lia;apply coding_add_zero.
  -rewrite(HF 7 ltac:(lia)ltac:(lia)ltac:(lia));unfold mid;rewrite program230_stack_register by lia;reflexivity.
  -intros i Hi Hi1 Hi2 Hi6 Hi7;rewrite(HF i Hi Hi1 Hi6);unfold mid;rewrite program230_stack_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 2)Hi2),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7). }
 rewrite EL in HTM.
 destruct(p230_program_history_join M j k(addM M N K)l m(program230_transfer_time M value)_ mid HJ HTJ HM)
 as[u[v[HU[Hpre Hpost]]]].
 exists u,v,(addM M(addM M N K)(program230_transfer_time M value));split;[exact HU|]. split.
 -exact(proj1(Hpost _ _(coding_lt_succ M _))HTM).
 -apply program230_positive_sum;apply program230_positive_sum;exact HN.
Qed.
Print Assumptions p230_mp_prefix_history.
