(** Exact finite unpair occurrences of the unchanged public p230 tree. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230Histories Program230TransferProgram
 Program230UnpairShape Program230UnpairShapeBody Program230HistoryPositive.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_unpair_sites:list(list bool*nat*nat):=[
 ([true;false;false;false],8,12);
 ([true;true;false;false;false],8,26);
 ([true;true;true;false;true;false;false;true;false;false;true;false;false;true;false;false;false],2,102);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;false;false;false],8,132);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;true;false;false;false],8,192);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;true;true;false;false],2,205);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;true;false;false],2,257);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;true;false;false],2,336);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;true;false;false;false],2,416);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;true;true;false;false],2,442);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;false;false;false],2,469);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;true;false;false;false],2,549);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;true;false;false;false],2,630);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;true;false;false;false],2,716);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;false;false;false;false],2,745);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;false;true;false;false],2,771);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;true;false;false;false],2,876);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;false;true;false;false],2,925);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;false;false;false;false],2,953);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;true;true;false;false],2,1000);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;false;false;false],2,1054);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;true;false;false;false],2,1134);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;true;false;false;false],2,1215);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;true;false;false;false],2,1296);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;false;false;false;false],2,1325);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;false;true;false;false],2,1351);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;false;false;false;false;false],2,1456);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;false;true;false;false],2,1483);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;true;false;false;false],2,1593);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;false;false;false;false;false],2,1623);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false],2,1650);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;true;false;false;false],2,1730);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;true;false;false;false],2,1812);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;true;false;false;false],2,1891);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;false;false;false;false],2,1920);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;false;true;false;false],2,1946);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;true;false;false;false],2,2049);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;true;true;false;false;false],2,2076);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;true;false;false;false],2,2158);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;true;false;false;false],2,2239);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;false;false;false;false],2,2268);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;false;true;false;false],2,2294);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;true;false;false;false],2,2400);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;false;true;false;false],2,2449);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;false;false;false;false],2,2477);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;true;true;false;false],2,2524);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;true;false;false;false],2,2656);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;false;false;false],2,2685);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;true;false;false;false],2,2791);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;true;false;false;false],2,2975);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;true;false;false;false],2,3054);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;false;false;false;false],2,3083);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;false;true;false;false;false],2,3110);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;true;false;false;false],2,3294);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;false;false],2,3342);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;false;false;false],2,3369);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;true;true;false;false],2,3415);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;false;true;false;false],2,3462);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;false;false;false;false],2,3490);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;true;true;false;false],2,3537);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;false;false;false;false],2,3565);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;false;true;false;false;false],2,3592);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;false;false;false;false],2,3622);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;false;true;false;false;false],2,3649);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;false;true;false;false],2,3698);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;false;false;false],2,3725);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;true;true;false;false],2,3771);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;false;true;false;false],2,3818);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;false;false;false;false],2,3846);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;true;true;false;false],2,3893);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;false;false;false;false],2,3921);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;false;true;false;false;false],2,3948);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;false;true;false;false],2,3997);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;false;false;false],2,4024);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;true;true;false;false],2,4070);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;false;true;false;false],2,4117);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;false;false;false;false],2,4145);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;true;true;false;false],2,4192);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;true;false;false;false],2,4273);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;true;false;false;false],2,4379);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;false;false;false;false;false],2,4408);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;false;true;false;false],2,4435);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;true;false;false;false],2,4515);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;true;false;false;false],2,4624);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;false;false;false;false;false],2,4654);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;false;true;false;false],2,4681);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;false;true;false;false],2,4729);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;false;false;false],2,4756);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;true;true;false;false],2,4802);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;false;true;false;false],2,4850);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;false;false;false],2,4877);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;true;true;false;false],2,4923);
 ([true;true;true;false;true;false;false;true;false;true;true;true;false;false],2,4996);
 ([true;true;true;true;false;false;true;false;false],2,5062)].
Definition p230_unpair_site_checked(entry:list bool*nat*nat):Prop:=
 let '(P,a,n):=entry in
 (a<9)%nat /\a<>6 /\a<>7 /\(length P<=40)%nat /\P<>inc_path P /\
 program230_unpair_occurrence P a n(S n)(S(S n))(S(S(S n)))
 (S(S(S(S n))))(S(S(S(S(S n)))))(S(S(S(S(S(S n)))))).
Lemma p230_unpair_sites_checked:Forall p230_unpair_site_checked p230_unpair_sites.
Proof. unfold p230_unpair_sites;repeat (apply Forall_cons;[vm_compute;repeat constructor;congruence|]);constructor. Qed.
Theorem p230_unpair_site_history M P a n start count:
 In(P,a,n)p230_unpair_sites->
 program230_pc start=program230_path_value M P->program230_register start a=count->
 program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(inc_path P) /\program230_register final a=zeroM M /\
 pair_graph M(program230_register final 6)(program230_register final 7)count /\
 (forall i,(i<9)%nat->i<>a->i<>6->i<>7->program230_register final i=program230_register start i).
Proof.
 intros Hin HP HA H6 H7.
 pose proof(proj1(Forall_forall p230_unpair_site_checked p230_unpair_sites)p230_unpair_sites_checked
 (P,a,n)Hin)as Hfacts.
 destruct Hfacts as[Ha[Ha6[Ha7[Hlen[Hneq HO]]]]].
 destruct(program230_unpair_shape_history M P a n(S n)(S(S n))(S(S(S n)))
 (S(S(S(S n))))(S(S(S(S(S n)))))(S(S(S(S(S(S n))))))Ha Ha6 Ha7 HO start count HP HA H6 H7)
 as[b[c[time[final[HR[HT[Hpc[Hz[Hpair Hframe]]]]]]]]].
 assert(Hpositive:coding_lt M(zeroM M)time).
 {eapply(program230_program_history_positive M p230 b c time start final HR HT).
  rewrite HP,Hpc;intro E;apply Hneq;exact(program230_path_value_injective M P(inc_path P)E). }
 exists b,c,time,final;split;[exact HR|]. split;[exact HT|]. split;[exact Hpositive|].
 split;[exact Hpc|]. split;[exact Hz|]. split;assumption.
Qed.
Print Assumptions p230_unpair_sites_checked.
Print Assumptions p230_unpair_site_history.
