(** The genuine MP histories discharge the numerical search-kernel MP case. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing SearchStep
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230RootReady Program230TransferProgram Program230StackStates Program230Selector
 Program230ComparisonIteration Program230SearchState Program230SearchPrefix
 Program230SearchActionDispatch Program230SearchActionFacts Program230MPTest Program230MPAction.
Unset Implicit Arguments.
Theorem p230_search_mp_kernel M s t pl np d:
 search_common_relation M t pl np d->search_h t=zeroM M->
 ((search_implication M(search_tw s)d(search_h s) /\search_tw t=d /\
   search_pair_graph M(zeroM M)(search_ws s)(search_ws t)) \/
  (~search_implication M(search_tw s)d(search_h s) /\search_tw t=zeroM M /\search_ws t=search_ws s))->
 p230_search_action_realizes M(p230_search_prefix_configuration M s np(zeroM M)pl d)t.
Proof.
 intros Hcommon Hh Hcase.
 destruct(p230_search_dispatch_mp M s np pl d)as[b[c[HR HT]]].
 set(start:=p230_search_action_start M s np(zeroM M)pl d p230_selector_mp)in *.
 eapply(p230_search_action_prepend M _ start t b c(code_numeral M 1)HR HT).
 destruct Hcase as[[Him[Htw Hws]]|[Him[Htw Hws]]].
 -apply search_pair_graph_correct in Hws;apply p230_search_implication_graph in Him.
  destruct(p230_mp_action_equal M start(search_tw s)(search_ws s)(search_h s)(search_ws t)Him eq_refl Hws)
  as[u[v[N[HU[HV HN]]]]].
  change(program230_program_history M K230.Prog230.p230 u v N
    (program230_stack_state start(program230_path_value M p230_selector_mp)(search_tw s)(search_ws s)(zeroM M)(zeroM M)))in HU.
  unfold start in HU;rewrite p230_search_action_clean in HU;fold start in HU.
  apply(proj2(p230_instruction_history_correct M u v N start))in HU.
  exists u,v,N,(program230_path_value M p230_mp_success_exit);split;[exact HU|]. split.
  +rewrite(p230_search_mp_state_matches M s t np pl d _ _ _ Hcommon Hh Htw eq_refl)in HV;exact HV.
  +split;[exact(proj1(p230_mp_return_ready M))|exact HN].
 -destruct(code_relation_total M(E_wim(CEvar 0)(CEvar 1))(arguments2(search_tw s)d(zeroM M)))as[value HV].
  assert(Hneq:value<>search_h s).
  {intro E;apply Him;apply p230_search_implication_graph;now rewrite <-E. }
  destruct(p230_mp_action_unequal M start(search_tw s)(search_ws s)value HV Hneq)
  as[u[v[N[HU[HE HN]]]]].
  change(program230_program_history M K230.Prog230.p230 u v N
    (program230_stack_state start(program230_path_value M p230_selector_mp)(search_tw s)(search_ws s)(zeroM M)(zeroM M)))in HU.
  unfold start in HU;rewrite p230_search_action_clean in HU;fold start in HU.
  apply(proj2(p230_instruction_history_correct M u v N start))in HU.
  exists u,v,N,(program230_path_value M p230_mp_unequal_exit);split;[exact HU|]. split.
  +rewrite(p230_search_mp_state_matches M s t np pl d _ _ _ Hcommon Hh Htw Hws)in HE;exact HE.
  +split;[exact(proj2(p230_mp_return_ready M))|exact HN].
Qed.
Print Assumptions p230_search_mp_kernel.
