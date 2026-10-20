(** The AX kernel branch consumes the one remaining explicit action contract. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing SearchStep
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230RootHistory Program230RootReady Program230TransferStates Program230TransferProgram
 Program230MPTransport Program230Selector Program230SelectorReturn Program230AXContract
 Program230SearchState Program230SearchPrefix Program230SearchActionDispatch Program230SearchActionFacts.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_search_ax_kernel M:
 p230_ax_action_contract M->forall s t pl np ac d code y pl4 u pl5 bound,
 search_add_graph M code(code_numeral M 3)ac->
 search_pair_graph M y pl4 pl->search_pair_graph M u pl5 pl4->
 search_add_graph M(search_h s)y bound->
 search_pl t=pl5->search_np t=np->search_d t=zeroM M->search_h t=zeroM M->
 search_stack M d(search_h s)bound code u(search_tw s)(search_ws s)(search_ws t)->
 (((code=d \/code=bound) /\search_tw t=zeroM M) \/
  (code<>d /\code<>bound /\search_bundle M d bound code(search_tw t)))->
 p230_search_action_realizes M(p230_search_prefix_configuration M s np ac pl d)t.
Proof.
 intros HX s t pl np ac d code y pl4 u pl5 bound Hac Hy Hu Hb Hpl Hnp Hd Hh Hstack Hgate.
 apply search_add_graph_correct in Hac;apply search_add_graph_correct in Hb.
 apply search_pair_graph_correct in Hy;apply search_pair_graph_correct in Hu.
 assert(Eac:ac=succM M(succM M(succM M code))).
 {rewrite Hac,(add_comm M code(code_numeral M 3));change(addM M(succM M(succM M(succM M(zeroM M))))code=succM M(succM M(succM M code))).
  now rewrite !add_succ,add_zero. }
 subst ac.
 destruct(p230_search_dispatch_ax M s np pl d code)as[b[c[HR HT]]].
 set(start:=p230_selector_cfg(p230_search_prefix_configuration M s np(succM M(succM M(succM M code)))pl d)
 (program230_path_value M p230_selector_ax)code).
 destruct(HX start y pl4 u pl5 bound(search_tw t)(search_ws t)eq_refl eq_refl eq_refl Hy Hu Hb Hstack Hgate)
 as[e[f[K[HE[HTE HK]]]]].
 apply(proj1(p230_instruction_history_correct M e f K start))in HE.
 destruct(p230_positive_history_entry M p230_selector_ax p230_selector_ax_short start _ e f K eq_refl
 (ipeq_sym _ _ p230_selector_ax_entry_ipeq)HE HTE HK)as[g[h[HG HTH]]].
 apply(proj2(p230_instruction_history_correct M g h K _))in HG.
 assert(Est:program230_with_pc start(program230_path_value M p230_selector_ax_short)=
 p230_selector_cfg(p230_search_prefix_configuration M s np(succM M(succM M(succM M code)))pl d)
 (program230_path_value M p230_selector_ax_short)code).
 {unfold start,p230_selector_cfg,program230_transfer_state,program230_config_of,program230_with_pc;reflexivity. }
 rewrite Est in HG.
 assert(Eout:p230_ax_result M start(search_tw t)(search_ws t)pl5=
 p230_search_embedding(zeroM M)(program230_path_value M p230_selector_return_exit)t).
 {unfold p230_ax_result,start,p230_selector_cfg,p230_search_prefix_configuration,
 program230_transfer_state,program230_config_of,p230_search_embedding;cbn.
 now rewrite Hpl,Hnp,Hd,Hh. }
 rewrite Eout in HTH.
 rewrite Eac;eapply(p230_search_action_prepend M _ _ t b c(code_numeral M 3)HR HT).
 exists g,h,K,(program230_path_value M p230_selector_return_exit);split;[exact HG|].
 split;[exact HTH|]. split;[apply p230_selector_return_ready|exact HK].
Qed.
Print Assumptions p230_search_ax_kernel.
