(** Actual root-ready candidate fetch followed by the two prefix reads. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230RootReady Program230RootHistory Program230PathCode Program230ReadSites
 Program230Copy2States Program230TransferStates Program230RotatedRestore
 Program230CandidateFetch Program230CandidateEntry Program230PrefixReads Program230UnpairRestore.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma p230_prefix_result_fetch M base pc np pl ac x rest:
 p230_prefix_result M(p230_fetch_cfg M base pc np pl)
 (program230_register(p230_fetch_cfg M base pc np pl)0)ac x rest =
 p230_prefix_result M base np ac x rest.
Proof. destruct base;reflexivity. Qed.

Lemma p230_prefix_after_fetch M base pc np pl Q ac pl2 x pl3 b c N:
 pc=program230_path_value M Q ->ipeq Q p230_read174_path ->
 program230_register base 3=zeroM M ->program230_register base 7=zeroM M ->
 pair_graph M ac pl2 pl ->pair_graph M x pl3 pl2 ->
 program230_history M p230_instruction_formula b c N base ->
 program230_state_at M b c N(p230_fetch_cfg M base pc np pl) ->
 exists f g total,program230_history M p230_instruction_formula f g total base /\
 program230_state_at M f g total(p230_prefix_result M base np ac x pl3) /\
 coding_lt M(zeroM M)total.
Proof.
 intros HP HQ H3 H7 HA HX HR HT.
 assert(Hpc:program230_pc(p230_fetch_cfg M base pc np pl)=program230_path_value M Q)by exact HP.
 assert(HF3:program230_register(p230_fetch_cfg M base pc np pl)3=zeroM M).
 {unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;exact H3. }
 assert(HF6:program230_register(p230_fetch_cfg M base pc np pl)6=zeroM M).
 {unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;reflexivity. }
 assert(HF7:program230_register(p230_fetch_cfg M base pc np pl)7=zeroM M).
 {unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;exact H7. }
 assert(HFA:pair_graph M ac pl2(program230_register(p230_fetch_cfg M base pc np pl)8)).
 {unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;exact HA. }
 destruct(p230_prefix_two_reads M Q(p230_fetch_cfg M base pc np pl)ac pl2 x pl3
 Hpc HQ HF3 HF6 HF7 HFA HX)as[d[e[K[HD[HE HK]]]]].
 rewrite p230_prefix_result_fetch in HE.
 destruct(program230_history_join M p230_instruction_formula b c N d e K base
 (p230_fetch_cfg M base pc np pl)HR HT HD)as[f[g[HJ[HL Hright]]]].
 exists f,g,(addM M N K);split;[exact HJ|]. split.
 -apply(proj1(Hright K _(coding_lt_succ M K)));exact HE.
 -rewrite(Arithmetic.add_comm M N K);apply program230_positive_sum;exact HK.
Qed.

Definition p230_candidate_choice M start np pl:=
 (program230_register start 8=zeroM M /\np=succM M(program230_register start 0) /\pl=program230_register start 0) \/
 (exists q,program230_register start 8=succM M q /\np=program230_register start 0 /\pl=q).

Theorem p230_root_prefix_history M start np pl ac pl2 x pl3:
 program230_root_ready M(program230_pc start) ->
 program230_register start 3=zeroM M ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 p230_candidate_choice M start np pl ->
 pair_graph M ac pl2 pl ->pair_graph M x pl3 pl2 ->
 exists b c time,program230_history M p230_instruction_formula b c time start /\
 program230_state_at M b c time(p230_prefix_result M start np ac x pl3) /\
 coding_lt M(zeroM M)time.
Proof.
 intros Hready H3 H6 H7 HC HA HX.
 destruct HC as[[H8[-> ->]]|[q[H8[-> ->]]]].
 -destruct(p230_candidate_fetch_zero_entry M start Hready H6 H8)as[b[c[HR HT]]].
  eapply(p230_prefix_after_fetch M start(program230_path_value M p230_rotated_exit)
   (succM M(program230_register start 0))(program230_register start 0)
   p230_rotated_exit ac pl2 x pl3 b c(p230_fetch_time M(program230_register start 0)));
   try eassumption;[reflexivity|].
  change(ipeq(p230_read174_path++[false;false])p230_read174_path).
  replace(p230_read174_path++[false;false])with((p230_read174_path++[false])++[false])by(rewrite <-app_assoc;reflexivity).
  eapply ipeq_trans;apply ipeq_app_false.
 -destruct(p230_candidate_fetch_positive_entry M start q Hready H6 H8)as[b[c[HR HT]]].
  eapply(p230_prefix_after_fetch M start(program230_path_value M([true]))
   (program230_register start 0)q([true])ac pl2 x pl3 b c(code_numeral M 2));
   try eassumption;[reflexivity|].
  apply ipeq_sym;change(ipeq(([true])++[false])([true]));apply ipeq_app_false.
Qed.

Theorem p230_root_prefix_total M start:
 program230_root_ready M(program230_pc start) ->
 program230_register start 3=zeroM M ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 exists np pl ac pl2 x pl3 b c time,
 p230_candidate_choice M start np pl /\pair_graph M ac pl2 pl /\pair_graph M x pl3 pl2 /\
 program230_history M p230_instruction_formula b c time start /\
 program230_state_at M b c time(p230_prefix_result M start np ac x pl3) /\
 coding_lt M(zeroM M)time.
Proof.
 intros HR H3 H6 H7.
 assert(HC:exists np pl,p230_candidate_choice M start np pl).
 {destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
   (fun ax H rho=>axioms M ax rho H)(program230_register start 8))as[E|[q E]].
  -exists(succM M(program230_register start 0)),(program230_register start 0);left;auto.
  -exists(program230_register start 0),q;right;exists q;auto. }
 destruct HC as[np[pl HC]]. destruct(pair_surjective M pl)as[ac[pl2 HA]].
 destruct(pair_surjective M pl2)as[x[pl3 HX]].
 destruct(p230_root_prefix_history M start np pl ac pl2 x pl3 HR H3 H6 H7 HC HA HX)
 as[b[c[time[HH[HT HP]]]]].
 exists np,pl,ac,pl2,x,pl3,b,c,time;exact(conj HC(conj HA(conj HX(conj HH(conj HT HP))))).
Qed.
Print Assumptions p230_prefix_after_fetch.
Print Assumptions p230_root_prefix_history.
Print Assumptions p230_root_prefix_total.
