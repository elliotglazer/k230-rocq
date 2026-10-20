(** Exact zero-padded selector entry after the numerical-search prefix. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SearchStep
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230RootHistory Program230TransferStates Program230Selector Program230PrefixReads
 Program230SearchState Program230SearchPrefix.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_search_dispatch_entry M s np ac pl d entry value b c time:
 program230_history M p230_instruction_formula b c time
 (p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)
 (program230_path_value M p230_selector_path)ac)->
 program230_state_at M b c time
 (p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)
 (program230_path_value M entry)value)->coding_lt M(zeroM M)time->
 exists u v,program230_history M p230_instruction_formula u v time
 (p230_search_prefix_configuration M s np ac pl d) /\
 program230_state_at M u v time
 (p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)
 (program230_path_value M entry)value).
Proof.
 intros HR HT Hpos.
 assert(Hnz:time<>zeroM M).
 {intro E;rewrite E in Hpos;destruct Hpos as[x Hx];rewrite coding_add_zero in Hx;exact(zero_ne_succ M x Hx). }
 destruct(p230_history_ipeq_endpoint M b c time
 (p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)(program230_path_value M p230_selector_path)ac)
 p230_selector_path p230_prefix_exit
 (p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)(program230_path_value M entry)value)
 eq_refl(ipeq_sym _ _ p230_prefix_exit_ipeq)HR Hnz HT)as[u[v[HU[HV _]]]].
 assert(E:program230_with_pc
 (p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)(program230_path_value M p230_selector_path)ac)
 (program230_path_value M p230_prefix_exit)=p230_search_prefix_configuration M s np ac pl d).
 {unfold p230_search_prefix_configuration,p230_selector_cfg,program230_transfer_state,program230_config_of,program230_with_pc;reflexivity. }
 rewrite E in HU;exists u,v;exact(conj HU HV).
Qed.
Theorem p230_search_dispatch_mp M s np pl d:
 exists b c,program230_history M p230_instruction_formula b c(code_numeral M 1)
 (p230_search_prefix_configuration M s np(zeroM M)pl d) /\
 program230_state_at M b c(code_numeral M 1)
 (p230_selector_cfg(p230_search_prefix_configuration M s np(zeroM M)pl d)(program230_path_value M p230_selector_mp)(zeroM M)).
Proof.
 destruct(p230_selector_dispatch_mp M(p230_search_prefix_configuration M s np(zeroM M)pl d))as[b[c[HR HT]]].
 eapply p230_search_dispatch_entry;[exact HR|exact HT|apply coding_zero_lt_succ].
Qed.
Theorem p230_search_dispatch_drop M s np pl d:
 exists b c,program230_history M p230_instruction_formula b c(code_numeral M 2)
 (p230_search_prefix_configuration M s np(code_numeral M 1)pl d) /\
 program230_state_at M b c(code_numeral M 2)
 (p230_selector_cfg(p230_search_prefix_configuration M s np(code_numeral M 1)pl d)(program230_path_value M p230_selector_drop)(zeroM M)).
Proof.
 destruct(p230_selector_dispatch_drop M(p230_search_prefix_configuration M s np(code_numeral M 1)pl d))as[b[c[HR HT]]].
 eapply p230_search_dispatch_entry;[exact HR|exact HT|apply coding_zero_lt_succ].
Qed.
Theorem p230_search_dispatch_nip M s np pl d:
 exists b c,program230_history M p230_instruction_formula b c(code_numeral M 3)
 (p230_search_prefix_configuration M s np(code_numeral M 2)pl d) /\
 program230_state_at M b c(code_numeral M 3)
 (p230_selector_cfg(p230_search_prefix_configuration M s np(code_numeral M 2)pl d)(program230_path_value M p230_selector_nip)(zeroM M)).
Proof.
 destruct(p230_selector_dispatch_nip M(p230_search_prefix_configuration M s np(code_numeral M 2)pl d))as[b[c[HR HT]]].
 eapply p230_search_dispatch_entry;[exact HR|exact HT|apply coding_zero_lt_succ].
Qed.
Theorem p230_search_dispatch_ax M s np pl d ac:
 exists b c,program230_history M p230_instruction_formula b c(code_numeral M 3)
 (p230_search_prefix_configuration M s np(succM M(succM M(succM M ac)))pl d) /\
 program230_state_at M b c(code_numeral M 3)
 (p230_selector_cfg(p230_search_prefix_configuration M s np(succM M(succM M(succM M ac)))pl d)(program230_path_value M p230_selector_ax_short)ac).
Proof.
 destruct(p230_selector_dispatch_ax M(p230_search_prefix_configuration M s np(succM M(succM M(succM M ac)))pl d)ac)as[b[c[HR HT]]].
 eapply p230_search_dispatch_entry;[exact HR|exact HT|apply coding_zero_lt_succ].
Qed.
Print Assumptions p230_search_dispatch_entry.
Print Assumptions p230_search_dispatch_mp.
Print Assumptions p230_search_dispatch_drop.
Print Assumptions p230_search_dispatch_nip.
Print Assumptions p230_search_dispatch_ax.
