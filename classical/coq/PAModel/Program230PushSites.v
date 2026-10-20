(** Every literal pushwff171 occurrence of p230. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230TransferProgram Program230StackStates
 Program230PairShape Program230PairSites Program230PushParts Program230Push.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_push_node_graph P n:=
 fol p230(ENode(root p230))P=Some(ENode n) /\
 nodes p230 n=(ENode(n+1),ENode(n+3)) /\
 nodes p230(n+1)=(EDecnz 1,ENode(n+2)) /\nodes p230(n+2)=(EInc 6,EContinue 2) /\
 nodes p230(n+3)=(ENode(n+4),ENode(n+6)) /\
 nodes p230(n+4)=(EDecnz 2,ENode(n+5)) /\nodes p230(n+5)=(EInc 1,EContinue 2) /\
 nodes p230(n+6)=(ENode(n+7),ENode(n+16)) /\
 program230_pair_node_graph(P++[true;true;false])(n+7) /\
 nodes p230(n+16)=(EDecnz 7,ENode(n+17)) /\nodes p230(n+17)=(EInc 2,EContinue 2).
Lemma program230_push_node_shape P n:program230_push_node_graph P n->program230_push_shape P.
Proof.
 intros[H0[Hn[H1[H2[H3[H4[H5[H6[Hpair[H16 H17]]]]]]]]]].
 assert(F:forall Q,fol p230(ENode(root p230))(P++Q)=fol p230(ENode n)Q).
 {intro Q;now rewrite fol_app,H0. }
 split.
 -exists(n+1),(n+2);unfold program230_transfer_occurrence;split.
  +rewrite F;cbn[fol child];rewrite Hn;reflexivity.
  +split;assumption.
 -split.
  +exists(n+4),(n+5);unfold program230_transfer_occurrence;split.
   *rewrite F;cbn[fol child];rewrite Hn;cbn[fol child snd];rewrite H3;reflexivity.
   *split;assumption.
  +split.
   *exact(program230_pair_node_shape(P++[true;true;false])(n+7)Hpair).
   *exists(n+16),(n+17);unfold program230_transfer_occurrence;split.
    --rewrite F;cbn[fol child];rewrite Hn;cbn[fol child snd];rewrite H3;cbn[fol child snd];rewrite H6;reflexivity.
    --split;assumption.
Qed.
Definition p230_push_site_rows:list(list bool*nat):=[
 ([true;true;true;false;true;false;false;true;false;false;true;false;false;false;false],49);
 ([true;true;true;false;true;false;false;true;false;false;true;false;false;false;true;true;false],75);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;false;false;false],147);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;false;true],171);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;false;false],231);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;false;false],285);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;true;false],310);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;false;false],364);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;true;false],389);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;false;false],496);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;false;false],522);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;false;false],579);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;true],603);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;false],663);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;true;true;false],689);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;true;false],796);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;false;false],824);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;true;false],849);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;false;false;false],905);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;true;false;false],980);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;true;false],1025);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;false;false],1081);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;false;false],1107);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;false;false],1164);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;true],1188);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;false],1243);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;true;true;false],1269);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;true;false],1376);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;false;false],1402);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;true;false],1427);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;false;false],1513);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;false;false],1541);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;true;false],1566);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;false],1677);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;true;false],1703);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;false;false],1759);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;false;false],1785);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;false;false],1840);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;true],1864);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;true;false],1971);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;false;false],1997);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;true;false],2022);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;false],2105);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;true;true;false],2131);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;false;false],2187);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;true;false],2212);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;true;false],2319);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;false],2347);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;true;true;false],2373);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;false;false;false],2429);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;true;false;false],2504);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;true;false],2549);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;false;false],2577);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;false;false],2604);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;true;false],2629);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;false;false],2712);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;false;false],2739);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;true;false],2764);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;false;false],2817);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;true;false],2842);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;false;false],2870);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;true;false],2895);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;false;false],2922);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;false;false],2948);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;false;false],3003);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;true],3027);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;false;false],3139);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;true;false],3164);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;false;false],3190);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;true;false],3215);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;false;false],3242);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;true;false],3267);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;false;false;false],3322);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;true;false;false],3395);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;false;false;false],3442);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;true;false;false],3517);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;false;false;false],3678);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;true;false;false],3751);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;false;false;false],3798);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;true;false;false],3873);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;false;false;false],3977);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;true;false;false],4050);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;false;false;false],4097);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;true;false;false],4172);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;false],4220);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;true;true;false],4246);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;false;false],4299);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;false],4326);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;true;true;false],4352);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;false],4462);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;true;true;false],4488);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;false;false],4544);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;false],4571);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;true;true;false],4597);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;false;false;false],4709);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;true;false;false],4782);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;false;false;false],4830);
 ([true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;true;false;false],4903);
 ([true;true;true;false;true;false;true;false],5008);
 ([true;true;true;true;false;false;false;false],5036);
 ([true;true;true;true;true;true;false],5100)].

Lemma p230_push_site_count:length p230_push_site_rows=101.
Proof. reflexivity. Qed.
Lemma p230_push_site_rows_correct:
 Forall(fun row=>program230_push_node_graph(fst row)(snd row))p230_push_site_rows.
Proof. unfold p230_push_site_rows;repeat(apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Definition p230_push_site P:=exists n,In(P,n)p230_push_site_rows.
Theorem p230_push_site_history M P base tw ws value:
 p230_push_site P->pair_graph M tw ws value->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M P)tw ws(zeroM M)(zeroM M)) /\
 Program230Configurations.program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(P++[true;true;true])))
   (zeroM M)value(zeroM M)(zeroM M)) /\coding_lt M(zeroM M)time.
Proof.
 intros[n HI]HP.
 pose proof(proj1(Forall_forall _ _)p230_push_site_rows_correct(P,n)HI)as H.
 exact(program230_push_history M P(program230_push_node_shape P n H)base tw ws value HP).
Qed.
Print Assumptions p230_push_site_rows_correct.
Print Assumptions p230_push_site_history.
