(** The two literal prefix reads, including their actual zero-padded control exit. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230TransferProgram Program230TransferEntry Program230SemanticHistories Program230ReadSites
 Program230RootHistory Program230PathCode Program230Selector Program230UnpairRestore.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma p230_prefix_read_padded M P Q a r start x y:
 p230_read_site P a r -> program230_pc start=program230_path_value M Q -> ipeq Q P ->
 pair_graph M x y(program230_register start a) ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 p230_read_effect M P a r start x y.
Proof.
 intros HS HP HQ Hpair H6 H7.
 set(canonical:=program230_with_pc start(program230_path_value M P)).
 destruct(p230_read_site_history M P a r canonical x y HS eq_refl Hpair H6 H7)
 as[b[c[N[final[HR[HT[HN[Hpc[Ha[Hr[HF6[HF7 HF]]]]]]]]]]]].
 apply(proj2(p230_instruction_history_correct M b c N canonical))in HR.
 assert(Hnz:N<>zeroM M).
 {intro E;rewrite E in HN;destruct HN as[d Hd];rewrite coding_add_zero in Hd;exact(zero_ne_succ M d Hd). }
 destruct(p230_history_ipeq_endpoint M b c N canonical P Q final eq_refl
 (ipeq_sym Q P HQ)HR Hnz HT)as[d[e[HD[HE _]]]].
 assert(EC:program230_with_pc canonical(program230_path_value M Q)=start).
 {unfold canonical;rewrite program230_with_pc_twice;now apply program230_with_pc_restore. }
 exists d,e,N,final;split;[apply p230_instruction_history_correct;now rewrite <-EC|].
 split;[exact HE|]. split;[exact HN|]. split;[exact Hpc|]. split;[exact Ha|].
 split;[exact Hr|]. split;[exact HF6|]. split;[exact HF7|exact HF].
Qed.

Definition p230_prefix_exit:list bool:=p230_selector_path++[false].
Definition p230_prefix_result M(base:program230_configuration(carrier M))np ac x pl:=
 mkProgram230Configuration(carrier M)(program230_path_value M p230_prefix_exit)
 np(program230_register base 1)(program230_register base 2)ac
 (addM M(program230_register base 4)x)(program230_register base 5)
 (zeroM M)(zeroM M)pl.
Lemma p230_prefix_exit_ipeq:ipeq p230_prefix_exit p230_selector_path.
Proof. apply ipeq_app_false. Qed.

Theorem p230_prefix_two_reads M Q start ac pl2 x pl3:
 program230_pc start=program230_path_value M Q ->ipeq Q p230_read174_path ->
 program230_register start 3=zeroM M ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 pair_graph M ac pl2(program230_register start 8) ->pair_graph M x pl3 pl2 ->
 exists b c N,program230_history M p230_instruction_formula b c N start /\
 program230_state_at M b c N
  (p230_prefix_result M start(program230_register start 0)ac x pl3) /\
 coding_lt M(zeroM M)N.
Proof.
 intros HP HQ H3 H6 H7 Hpair Hpair2.
 destruct(p230_prefix_read_padded M p230_read174_path Q 8 3 start ac pl2
 p230_read174_site HP HQ Hpair H6 H7)
 as[b[c[N[mid[HR[HT[HN[Hpc[H8[Hm3[Hm6[Hm7 HF]]]]]]]]]]]].
 rewrite H3,coding_add_zero in Hm3.
 assert(Hentry:program230_pc mid=program230_path_value M p230_read175_path)by exact Hpc.
 rewrite <-H8 in Hpair2.
 destruct(p230_read_site_history M p230_read175_path 8 4 mid x pl3 p230_read175_site
 Hentry Hpair2 Hm6 Hm7)
 as[d[e[K[final[HD[HE[HK[Hfinalpc[Hfinal8[Hfinal4[Hfinal6[Hfinal7 HG]]]]]]]]]]]].
 destruct(p230_program_history_join M b c N d e K start mid HR HT HD)as[f[g[HJ[HL Hright]]]].
 assert(EF:final=p230_prefix_result M start(program230_register start 0)ac x pl3).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j].
  -exact Hfinalpc.
  -change(program230_register final j=program230_field
    (p230_prefix_result M start(program230_register start 0)ac x pl3)(S j)).
   destruct j as[|[|[|[|[|[|[|[|[|j]]]]]]]]];try lia;cbn[p230_prefix_result program230_field].
   +rewrite(HG 0 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));apply HF;lia.
   +rewrite(HG 1 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));apply HF;lia.
   +rewrite(HG 2 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));apply HF;lia.
   +rewrite(HG 3 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));exact Hm3.
   +rewrite Hfinal4,(HF 4 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));reflexivity.
   +rewrite(HG 5 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia));apply HF;lia.
   +exact Hfinal6.
   +exact Hfinal7.
   +exact Hfinal8. }
 exists f,g,(addM M N K);split;[apply(proj2(p230_instruction_history_correct M f g _ start));exact HJ|].
 split.
 -rewrite <-EF;apply(proj1(Hright K final(coding_lt_succ M K)));exact HE.
 -apply program230_positive_sum;exact HN.
Qed.
Print Assumptions p230_prefix_read_padded.
Print Assumptions p230_prefix_two_reads.
