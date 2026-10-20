(** Decode a list pair and restore its tail to the input register.
    This is the actual n158/n160 composition, at any certified occurrence. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs NumericalEnvironments Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferLoop Program230TransferProgram
 Program230SemanticHistories Program230UnpairSites Program230UnpairEntry.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_positive_sum M a b:
 coding_lt M(zeroM M)a->coding_lt M(zeroM M)(addM M a b).
Proof.
 intros[d Hd];rewrite coding_add_zero in Hd;rewrite Hd,Arithmetic.add_succ.
 exists(addM M d b);now rewrite coding_add_zero.
Qed.
Theorem p230_unpair_restore M P a un n m start x y:
 In(P++[false],a,un)p230_unpair_sites->
 program230_transfer_occurrence p230(P++[true])7 a n m->
 program230_pc start=program230_path_value M P->
 pair_graph M x y(program230_register start a)->
 program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(inc_path P++[false]) /\
 program230_register final 6=x /\program230_register final 7=zeroM M /\program230_register final a=y /\
 (forall i,(i<9)%nat->i<>a->i<>6->i<>7->program230_register final i=program230_register start i).
Proof.
 intros HI HO HP Hpair H6 H7.
 pose proof(proj1(Forall_forall p230_unpair_site_checked p230_unpair_sites)p230_unpair_sites_checked
 (P++[false],a,un)HI)as[Ha[Ha6[Ha7 _]]].
 destruct(p230_unpair_padded_entry M(P++[false])P a un start(program230_register start a)HI HP
 (ipeq_sym(P++[false])P(ipeq_app_false P))eq_refl H6 H7)
 as[b[c[N[mid[HN[HT[Hpos[Hpc[Ha0[Hxy Hframe]]]]]]]]]].
 destruct(pair_injective M(program230_register start a)(program230_register mid 6)(program230_register mid 7)x y Hxy Hpair)
 as[Hmx Hmy].
 rewrite inc_path_app_false in Hpc.
 destruct(program230_transfer_program_history M p230(P++[true])7 a n m mid y ltac:(lia)Ha
 ltac:(congruence)HO Hpc Hmy)as[d[e[final[HR[HE[HF[H70[Hay Hrest]]]]]]]].
 destruct(p230_program_history_join M b c N d e(program230_transfer_time M y)start mid HN HT HR)
 as[f[g[HG[Hleft Hright]]]].
 exists f,g,(addM M N(program230_transfer_time M y)),final;split;[exact HG|].
 split;[apply(proj1(Hright(program230_transfer_time M y)_(coding_lt_succ M(program230_transfer_time M y))));exact HE|].
 split;[apply program230_positive_sum;exact Hpos|].
 split;[now rewrite inc_path_app_true in HF|].
 split;[rewrite(Hrest 6 ltac:(lia)ltac:(lia)ltac:(congruence));exact Hmx|].
 split;[exact H70|]. split;[rewrite Hay,Ha0;apply coding_add_zero|].
 intros i Hi Hia Hi6 Hi7;rewrite(Hrest i Hi Hi7 Hia);exact(Hframe i Hi Hia Hi6 Hi7).
Qed.
Print Assumptions program230_positive_sum.
Print Assumptions p230_unpair_restore.
