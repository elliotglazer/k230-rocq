(** Actual halting-search macro: prefix, NIP dispatch, then the literal halt branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 SearchStep Program230Configurations Program230Histories Program230HistoryJoin
 Program230InstructionFormula Program230PathCode Program230RootHistory Program230RootReady
 Program230TransferStates Program230ComparisonIteration Program230Selector
 Program230PrefixReads Program230SearchPrefix Program230SearchState
 Program230NipHalting Program230UnpairRestore Program230HaltingSentence Program230SearchComparison.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem p230_search_halt_history M s pc:
 program230_root_ready M pc ->enumerator_halt M s ->
 exists b c time,program230_history M p230_instruction_formula b c time
  (p230_search_embedding(zeroM M)pc s) /\p230_counter_halt_at M b c time /\
 coding_lt M(zeroM M)time.
Proof.
 intros Hready[pl[np[ac[pl2[x[pl3[d[HP[Hac Hh]]]]]]]]].
 subst ac.
 destruct(p230_search_prefix_history M s pc pl np(code_numeral M 2)pl2 x pl3 d Hready HP)
 as[b[c[N[HR[HT HN]]]]].
 set(prefix:=p230_search_prefix_configuration M s np(code_numeral M 2)pl3 d)in *.
 destruct(p230_selector_dispatch_nip M prefix)as[f[g[HF HG]]].
 assert(Estart:program230_with_pc
  (p230_selector_cfg prefix(program230_path_value M p230_selector_path)(code_numeral M 2))
  (program230_path_value M p230_prefix_exit)=prefix).
 {unfold prefix,p230_search_prefix_configuration,p230_selector_cfg,program230_transfer_state,
   program230_config_of,program230_with_pc;reflexivity. }
 assert(Hnonzero:code_numeral M 3<>zeroM M).
 {intro E;exact(zero_ne_succ M(code_numeral M 2)(eq_sym E)). }
 destruct(p230_history_ipeq_endpoint M f g(code_numeral M 3)
  (p230_selector_cfg prefix(program230_path_value M p230_selector_path)(code_numeral M 2))
  p230_selector_path p230_prefix_exit
  (p230_selector_cfg prefix(program230_path_value M p230_selector_nip)(zeroM M))
  eq_refl(ipeq_sym _ _ p230_prefix_exit_ipeq)HF Hnonzero HG)
 as[f1[g1[HF1[HG1 _]]]].
 rewrite Estart in HF1.
 set(nip:=p230_selector_cfg prefix(program230_path_value M p230_selector_nip)(zeroM M))in *.
 destruct(p230_nip_action_reaches_halt M nip)as[h[i[K[HI[[last[HL HH]] HK]]]]].
 assert(Enip:program230_comparison_state nip(program230_path_value M p230_selector_nip)
  (zeroM M)(code_numeral M 1)=nip).
 {unfold nip,prefix,p230_search_prefix_configuration,p230_selector_cfg,program230_transfer_state,
   program230_config_of,program230_comparison_state;cbn;now rewrite Hh. }
 rewrite Enip in HI.
 destruct(program230_history_join M p230_instruction_formula b c N f1 g1(code_numeral M 3)
  _ prefix HR HT HF1)as[u[v[HU[HUleft HUright]]]].
 pose proof(proj1(HUright(code_numeral M 3)nip(coding_lt_succ M(code_numeral M 3)))HG1)as Hnip.
 destruct(program230_history_join M p230_instruction_formula u v(addM M N(code_numeral M 3))
  h i K _ nip HU Hnip HI)as[w[z[HW[HWleft HWright]]]].
 exists w,z,(addM M(addM M N(code_numeral M 3))K);split;[exact HW|]. split.
 -exists last;split;[exact(proj1(HWright K last(coding_lt_succ M K))HL)|exact HH].
 -apply program230_positive_sum;apply program230_positive_sum;exact HN.
Qed.

Theorem p230_actual_halt_search_macro M:p230_halt_search_macro M.
Proof.
 intros s pc Hpc HH;destruct(p230_search_halt_history M s pc Hpc HH)as[b[c[time[HR[HT _]]]]].
 exists b,c,time;exact(conj HR HT).
Qed.
Print Assumptions p230_search_halt_history.
Print Assumptions p230_actual_halt_search_macro.
