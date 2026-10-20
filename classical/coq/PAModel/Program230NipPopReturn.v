(** The actual NIP pop followed by its two literal selector-return instructions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230Configurations Program230Histories Program230InstructionFormula Program230PathCode
 Program230RootHistory Program230TransferEntry Program230TransferProgram Program230SemanticHistories
 Program230UnpairRestore Program230MPTransport Program230NipPop Program230ReadSites Program230Selector Program230SelectorReturn
 Program230ComparisonIteration.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_nip_action_pop_return M base h head tail:
 h<>code_numeral M 1->pair_graph M head tail(program230_register base 2)->program230_register base 7=zeroM M->
 exists b c time final,program230_history M p230_instruction_formula b c time
 (program230_comparison_state base(program230_path_value M p230_selector_nip)(zeroM M)h) /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M p230_selector_return_exit /\
 program230_register final 2=tail /\program230_register final 5=head /\
 program230_register final 6=zeroM M /\program230_register final 7=zeroM M /\
 (forall i,(i<9)%nat->i<>2->i<>5->i<>6->i<>7->program230_register final i=program230_register base i).
Proof.
 intros HH HP H7.
 destruct(p230_nip_action_pop M base h head tail HH HP H7)as[b[c[N[last[HR[HT[HN[Hpc[Hws[Hh[H6[H7f HF]]]]]]]]]]]].
 destruct(p230_selector_nip_return M last)as[d[e[HD HE]]].
 apply(proj1(p230_instruction_history_correct M d e(code_numeral M 2)_))in HD.
 assert(Hpad:ipeq(inc_path p230_selector_nip)(inc_path p230_pop170_path++[false])).
 {unfold p230_selector_nip,p230_pop170_path;vm_compute;unfold ipeq,bit;intro i;
 do 20(destruct i as[|i];[reflexivity|]);reflexivity. }
 destruct(p230_positive_history_entry M(inc_path p230_selector_nip)(inc_path p230_pop170_path++[false])
 (program230_with_pc last(program230_path_value M(inc_path p230_selector_nip)))_
 d e(code_numeral M 2)eq_refl Hpad HD HE(coding_zero_lt_succ M _))as[f[g[HG HHG]]].
 rewrite program230_with_pc_twice,(program230_with_pc_restore last _ Hpc)in HG.
 destruct(p230_program_history_join M b c N f g(code_numeral M 2)_ last HR HT HG)as[u[v[HU[HL HTail]]]].
 apply(proj2(p230_instruction_history_correct M u v(addM M N(code_numeral M 2))_))in HU.
 exists u,v,(addM M N(code_numeral M 2)),(program230_with_pc last(program230_path_value M p230_selector_return_exit));split;[exact HU|].
 split;[exact(proj1(HTail _ _(coding_lt_succ M _))HHG)|].
 split;[apply program230_positive_sum;exact HN|]. split;[reflexivity|].
 repeat rewrite program230_with_pc_register.
 split;[exact Hws|]. split;[exact Hh|]. split;[exact H6|]. split;[exact H7f|].
 intros i Hi Hi2 Hi5 Hi6 Hi7;rewrite program230_with_pc_register;exact(HF i Hi Hi2 Hi5 Hi6 Hi7).
Qed.
Print Assumptions p230_nip_action_pop_return.
