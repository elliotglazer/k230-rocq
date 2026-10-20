(** Literal numerical-search prefix relation is realized by the actual p230 prefix. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 SearchStep Program230Configurations Program230Histories Program230InstructionFormula
 Program230PathCode Program230RootReady Program230PrefixReads Program230Prefix Program230SearchState.
Unset Implicit Arguments.

Definition p230_search_prefix_configuration M(s:search_state(carrier M))np ac pl d:=
 mkProgram230Configuration(carrier M)(program230_path_value M p230_prefix_exit)
 np(search_tw s)(search_ws s)ac d(search_h s)(zeroM M)(zeroM M)pl.

Lemma p230_search_prefix_choice M s pc pl np ac pl2 x pl3 d:
 search_prefix_relation M s pl np ac pl2 x pl3 d ->
 p230_candidate_choice M(p230_search_embedding(zeroM M)pc s)np pl /\
 pair_graph M ac pl2 pl /\pair_graph M x pl3 pl2 /\d=addM M(search_d s)x.
Proof.
 intros[Hchoice[HA[HX HD]]]. apply search_pair_graph_correct in HA.
 apply search_pair_graph_correct in HX;apply search_add_graph_correct in HD.
 split;[|exact(conj HA(conj HX HD))].
 destruct Hchoice as[[Hz[Hp Hn]]|[Hp Hn]];unfold p230_candidate_choice.
 -apply search_add_graph_correct in Hn;left;repeat split;try assumption.
  change(np=succM M(search_np s));rewrite Hn;apply eq_sym;apply succ_as_add.
 -apply search_add_graph_correct in Hp;right;exists pl;split;[|split;[exact Hn|reflexivity]].
  change(search_pl s=succM M pl);rewrite Hp;apply eq_sym;apply succ_as_add.
Qed.

Theorem p230_search_prefix_history M s pc pl np ac pl2 x pl3 d:
 program230_root_ready M pc ->search_prefix_relation M s pl np ac pl2 x pl3 d ->
 exists b c time,
 program230_history M p230_instruction_formula b c time(p230_search_embedding(zeroM M)pc s) /\
 program230_state_at M b c time(p230_search_prefix_configuration M s np ac pl3 d) /\
 coding_lt M(zeroM M)time.
Proof.
 intros HR HP.
 destruct(p230_search_prefix_choice M s pc pl np ac pl2 x pl3 d HP)as[HC[HA[HX HD]]].
 destruct(p230_root_prefix_history M(p230_search_embedding(zeroM M)pc s)
 np pl ac pl2 x pl3 HR eq_refl eq_refl eq_refl HC HA HX)as[b[c[time[HH[HT HN]]]]].
 exists b,c,time;split;[exact HH|]. split;[|exact HN].
 rewrite HD;exact HT.
Qed.
Print Assumptions p230_search_prefix_choice.
Print Assumptions p230_search_prefix_history.
