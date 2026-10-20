(** Exact graph and record identifications for search-kernel actions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing SearchStep
 Program230PathCode Program230Configurations Program230Histories Program230HistoryJoin
 Program230InstructionFormula Program230RootReady Program230TransferStates Program230TransferProgram
 Program230PairConstructorIteration Program230Copy2States Program230StackStates Program230Selector Program230ComparisonIteration
 Program230SearchState Program230SearchPrefix Program230MPTest.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_search_action_realizes M start(t:search_state(carrier M)):=
 exists b c time pc,program230_history M p230_instruction_formula b c time start /\
 program230_state_at M b c time(p230_search_embedding(zeroM M)pc t) /\
 program230_root_ready M pc /\coding_lt M(zeroM M)time.
Lemma p230_search_action_prepend M start middle t b c time:
 program230_history M p230_instruction_formula b c time start->program230_state_at M b c time middle->
 p230_search_action_realizes M middle t->p230_search_action_realizes M start t.
Proof.
 intros HR HT[d[e[K[pc[HD[HE[HP HK]]]]]]].
 destruct(program230_history_join M p230_instruction_formula b c time d e K start middle HR HT HD)as[f[g[HF[HL HH]]]].
 exists f,g,(addM M time K),pc;split;[exact HF|]. split.
 -exact(proj1(HH K _(coding_lt_succ M K))HE).
 -split;[exact HP|apply program230_duration_add;exact HK].
Qed.
Lemma p230_search_implication_graph M a b z:
 search_implication M a b z<->implication_graph M a b z.
Proof.
 unfold search_implication,implication_graph;apply code_relation_ext.
 intro i;destruct i as[|[|[|i]]];reflexivity.
Qed.
Definition p230_search_action_start M s np ac pl d entry:=
 p230_selector_cfg(p230_search_prefix_configuration M s np ac pl d)
 (program230_path_value M entry)(zeroM M).
Lemma p230_search_mp_state_matches M s t np pl d pc tw ws:
 search_common_relation M t pl np d->search_h t=zeroM M->search_tw t=tw->search_ws t=ws->
 p230_mp_output_state M(p230_search_action_start M s np(zeroM M)pl d p230_selector_mp)pc tw ws=
 p230_search_embedding(zeroM M)pc t.
Proof.
 intros[Hpl[Hnp Hd]]Hh Htw Hws.
 unfold p230_mp_output_state,p230_search_action_start,p230_search_prefix_configuration,
 p230_selector_cfg,program230_stack_state,program230_copy2_state,program230_transfer_state,
 program230_config_of,program230_comparison_state,p230_search_embedding;cbn.
 now rewrite Hpl,Hnp,Hd,Hh,Htw,Hws.
Qed.
Lemma p230_search_action_clean M s np ac pl d entry:
 program230_stack_state(p230_search_action_start M s np ac pl d entry)(program230_path_value M entry)
 (search_tw s)(search_ws s)(zeroM M)(zeroM M)=p230_search_action_start M s np ac pl d entry.
Proof.
 unfold p230_search_action_start,p230_search_prefix_configuration,p230_selector_cfg,
 program230_stack_state,program230_copy2_state,program230_transfer_state,program230_config_of;reflexivity.
Qed.
Print Assumptions p230_search_action_prepend.
Print Assumptions p230_search_implication_graph.
Print Assumptions p230_search_mp_state_matches.
