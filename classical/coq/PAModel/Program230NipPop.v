(** Ordinary NIP action: the actual nonhalting branch followed by stack pop. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230Configurations Program230Histories Program230InstructionFormula Program230PathCode
 Program230TransferProgram Program230SemanticHistories Program230UnpairRestore Program230ReadSites
 Program230Selector Program230ComparisonIteration Program230ComparisonControl
 Program230NipHaltSite Program230NipHalting.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_nip_pop_entry:p230_nip_unequal_exit=p230_pop170_path.
Proof. reflexivity. Qed.
Theorem p230_nip_action_pop M base h head tail:
 h<>code_numeral M 1->pair_graph M head tail(program230_register base 2)->
 program230_register base 7=zeroM M->
 exists b c time final,
 program230_program_history M p230 b c time
 (program230_comparison_state base(program230_path_value M p230_selector_nip)(zeroM M)h) /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(inc_path p230_pop170_path++[false]) /\
 program230_register final 2=tail /\program230_register final 5=head /\
 program230_register final 6=zeroM M /\program230_register final 7=zeroM M /\
 (forall i,(i<9)%nat->i<>2->i<>5->i<>6->i<>7->program230_register final i=program230_register base i).
Proof.
 intros Hh Hpair H7.
 destruct(p230_nip_skip_halt M base h Hh)as[b[c[N[HR[HT Hpos]]]]].
 set(mid:=program230_comparison_state base(program230_path_value M p230_nip_unequal_exit)(zeroM M)(zeroM M)).
 assert(HP:program230_pc mid=program230_path_value M p230_pop170_path).
 {unfold mid;rewrite <-p230_nip_pop_entry;reflexivity. }
 assert(Hpm:pair_graph M head tail(program230_register mid 2)).
 {unfold mid;rewrite comparison_register by lia;exact Hpair. }
 assert(H6m:program230_register mid 6=zeroM M).
 {unfold mid;rewrite comparison_register by lia;reflexivity. }
 assert(H7m:program230_register mid 7=zeroM M).
 {unfold mid;rewrite comparison_register by lia;exact H7. }
 destruct(p230_read_site_history M p230_pop170_path 2 5 mid head tail p230_pop170_site HP Hpm H6m H7m)
 as[d[e[K[final[HD[HE[Hk[Hpc[Hws[Hp2[H6[H7f Hframe]]]]]]]]]]]].
 apply(proj1(p230_instruction_history_correct M b c N _))in HR.
 destruct(p230_program_history_join M b c N d e K _ mid HR HT HD)as[f[g[HF[HL HH]]]].
 exists f,g,(addM M N K),final;split;[exact HF|].
 split;[apply(proj1(HH K _ (coding_lt_succ M K)));exact HE|].
 split;[apply program230_positive_sum;exact Hpos|]. split;[exact Hpc|].
 split;[exact Hws|]. split.
 -rewrite Hp2;unfold mid;rewrite comparison_register by lia;apply coding_add_zero.
 -split;[exact H6|]. split;[exact H7f|].
  intros i Hi Hi2 Hi5 Hi6 Hi7. rewrite(Hframe i Hi Hi2 Hi5 Hi6 Hi7);unfold mid.
  rewrite comparison_register by exact Hi.
  now rewrite(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 5)Hi5).
Qed.
Print Assumptions p230_nip_pop_entry.
Print Assumptions p230_nip_action_pop.
