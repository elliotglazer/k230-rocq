(** Actual DROP and nonhalting NIP actions realize their numerical kernel clauses. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing SearchStep
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230RootReady Program230RootHistory Program230TransferStates Program230TransferProgram
 Program230Copy2States Program230StackStates Program230Selector Program230SelectorReturn
 Program230ComparisonIteration Program230SearchState Program230SearchPrefix
 Program230SearchActionDispatch Program230SearchActionFacts Program230DropAction Program230NipPopReturn.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_search_embedded_fields M final pc t:
 program230_pc final=pc->
 program230_register final 0=search_np t->program230_register final 1=search_tw t->
 program230_register final 2=search_ws t->program230_register final 3=zeroM M->
 program230_register final 4=search_d t->program230_register final 5=search_h t->
 program230_register final 6=zeroM M->program230_register final 7=zeroM M->
 program230_register final 8=search_pl t->final=p230_search_embedding(zeroM M)pc t.
Proof. destruct final;cbn;intros;subst;reflexivity. Qed.
Theorem p230_search_drop_kernel M s t pl np d:
 search_common_relation M t pl np d->search_tw t=search_h s->
 search_pair_graph M(search_tw s)(search_ws s)(search_ws t)->search_h t=search_h s->
 p230_search_action_realizes M(p230_search_prefix_configuration M s np(code_numeral M 1)pl d)t.
Proof.
 intros[Hpl[Hnp Hd]]Htw Hpair Hh;apply search_pair_graph_correct in Hpair.
 destruct(p230_search_dispatch_drop M s np pl d)as[b[c[HR HT]]].
 set(start:=p230_search_action_start M s np(code_numeral M 1)pl d p230_selector_drop)in *.
 eapply(p230_search_action_prepend M _ start t b c(code_numeral M 2)HR HT).
 destruct(p230_drop_action_returned M start(search_tw s)(search_ws s)(search_ws t)Hpair)
 as[u[v[N[HU[HV HN]]]]].
 unfold start in HU;rewrite p230_search_action_clean in HU;fold start in HU.
 assert(E:program230_stack_state start(program230_path_value M p230_selector_return_exit)
  (program230_register start 5)(search_ws t)(zeroM M)(zeroM M)=
  p230_search_embedding(zeroM M)(program230_path_value M p230_selector_return_exit)t).
 {unfold start,p230_search_action_start,p230_search_prefix_configuration,p230_selector_cfg,
  program230_stack_state,program230_copy2_state,program230_transfer_state,program230_config_of,p230_search_embedding;cbn.
  now rewrite Hpl,Hnp,Hd,Htw,Hh. }
 rewrite E in HV.
 exists u,v,N,(program230_path_value M p230_selector_return_exit);split;[exact HU|].
 split;[exact HV|]. split;[apply p230_selector_return_ready|exact HN].
Qed.
Theorem p230_search_nip_kernel M s t pl np d:
 search_h s<>code_numeral M 1->search_common_relation M t pl np d->search_tw t=search_tw s->
 search_pair_graph M(search_h t)(search_ws t)(search_ws s)->
 p230_search_action_realizes M(p230_search_prefix_configuration M s np(code_numeral M 2)pl d)t.
Proof.
 intros Hneq[Hpl[Hnp Hd]]Htw Hpair;apply search_pair_graph_correct in Hpair.
 destruct(p230_search_dispatch_nip M s np pl d)as[b[c[HR HT]]].
 set(start:=p230_search_action_start M s np(code_numeral M 2)pl d p230_selector_nip)in *.
 eapply(p230_search_action_prepend M _ start t b c(code_numeral M 3)HR HT).
 destruct(p230_nip_action_pop_return M start(search_h s)(search_h t)(search_ws t)Hneq Hpair eq_refl)
 as[u[v[N[final[HU[HV[HN[HP[Hws[Hh[H6[H7 HF]]]]]]]]]]]].
 assert(Estart:program230_comparison_state start(program230_path_value M p230_selector_nip)(zeroM M)(search_h s)=start).
 {unfold start,p230_search_action_start,p230_search_prefix_configuration,p230_selector_cfg,
 program230_transfer_state,program230_config_of,program230_comparison_state;reflexivity. }
 rewrite Estart in HU.
 assert(Efinal:final=p230_search_embedding(zeroM M)(program230_path_value M p230_selector_return_exit)t).
 {eapply p230_search_embedded_fields.
  -exact HP.
  -rewrite(HF 0 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));change(np=search_np t);symmetry;exact Hnp.
  -rewrite(HF 1 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));change(search_tw s=search_tw t);symmetry;exact Htw.
  -exact Hws.
  -rewrite(HF 3 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));reflexivity.
  -rewrite(HF 4 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));change(d=search_d t);symmetry;exact Hd.
  -exact Hh.
  -exact H6.
  -exact H7.
  -rewrite(HF 8 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));change(pl=search_pl t);symmetry;exact Hpl. }
 rewrite Efinal in HV.
 exists u,v,N,(program230_path_value M p230_selector_return_exit);split;[exact HU|].
 split;[exact HV|]. split;[apply p230_selector_return_ready|exact HN].
Qed.
Print Assumptions p230_search_embedded_fields.
Print Assumptions p230_search_drop_kernel.
Print Assumptions p230_search_nip_kernel.
