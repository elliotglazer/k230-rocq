(** Actual read/pop composition: decode a list, restore the tail, add the head to a target. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferLoop Program230TransferProgram
 Program230TransferEntry Program230SemanticHistories Program230UnpairSites Program230UnpairRestore Program230DecodeEntry.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_read_composition M P a r un dn dm rn rm start x y:
 In((P++[false])++[false],a,un)p230_unpair_sites->
 program230_transfer_occurrence p230((P++[false])++[true])7 a dn dm->
 program230_transfer_occurrence p230(P++[true])6 r rn rm->
 (r<9)%nat->r<>a->r<>6->r<>7->
 program230_pc start=program230_path_value M P->pair_graph M x y(program230_register start a)->
 program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(inc_path P++[false]) /\
 program230_register final a=y /\program230_register final r=addM M(program230_register start r)x /\
 program230_register final 6=zeroM M /\program230_register final 7=zeroM M /\
 (forall i,(i<9)%nat->i<>a->i<>r->i<>6->i<>7->program230_register final i=program230_register start i).
Proof.
 intros HI HD HR Hr Hra Hr6 Hr7 HP Hpair H6 H7.
 pose proof(proj1(Forall_forall p230_unpair_site_checked p230_unpair_sites)p230_unpair_sites_checked
 ((P++[false])++[false],a,un)HI)as[Ha[Ha6[Ha7 _]]].
 destruct(p230_decode_padded_entry M(P++[false])P a un dn dm start x y HI HD HP
 (ipeq_sym(P++[false])P(ipeq_app_false P))Hpair H6 H7)
 as[b[c[N[mid[HN[HT[Hpositive[Hpc[Hmx[Hm7[Hmy Hframe]]]]]]]]]]].
 rewrite inc_path_app_false in Hpc.
 destruct(p230_transfer_padded_entry M(P++[true])((P++[true])++[false])6 r rn rm mid x
 ltac:(lia)Hr ltac:(congruence)HR Hpc(ipeq_app_false(P++[true]))Hmx)
 as[d[e[final[Hrun[Hend[Hfinalpc[Hfinal6[Hfinalr Hrest]]]]]]]].
 destruct(p230_program_history_join M b c N d e(program230_transfer_time M x)start mid HN HT Hrun)
 as[f[g[Hjoined[Hleft Hright]]]].
 exists f,g,(addM M N(program230_transfer_time M x)),final;split;[exact Hjoined|].
 split;[apply(proj1(Hright(program230_transfer_time M x)_(coding_lt_succ M(program230_transfer_time M x))));exact Hend|].
 split;[apply program230_positive_sum;exact Hpositive|]. split;[now rewrite inc_path_app_true in Hfinalpc|].
 split;[rewrite(Hrest a Ha Ha6 ltac:(congruence));exact Hmy|].
 split;[rewrite Hfinalr,(Hframe r Hr Hra Hr6 Hr7);reflexivity|]. split;[exact Hfinal6|].
 split;[rewrite(Hrest 7 ltac:(lia)ltac:(lia)ltac:(congruence));exact Hm7|].
 intros i Hi Hia Hir Hi6 Hi7;rewrite(Hrest i Hi Hi6 Hir);exact(Hframe i Hi Hia Hi6 Hi7).
Qed.
Print Assumptions p230_read_composition.
