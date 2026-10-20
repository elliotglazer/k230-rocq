(** Actual graph-preserving histories for native AX parameter loads and input decoding. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230TransferStates Program230TransferProgram Program230ParameterLoad Program230ParameterSites Program230UnpairSites
 Program230AXSymbolic Program230AXSymbolicGraphs Program230AXRegisterGraph Program230AXGraphEffects
 Program230AXNativeSymbolic Program230AXRuntimeInterface.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_ax_parameter_runtime M env symbolic start P r:
 (r<9)%nat->r<>1->r<>6->program230_parameter_shape P r->
 program230_pc start=program230_path_value M P->program230_register start 1=zeroM M->
 program230_register start 6=zeroM M->p230_ax_register_graph M env symbolic start->
 p230_ax_runtime_result M env(p230_ax_set symbolic 1(program230_register symbolic r))start(inc_path(P++[true])).
Proof.
 intros Hr Hr1 Hr6 Hshape Hpc H1 H6 HG.
 destruct(program230_parameter_history M P r start Hr Hr1 Hr6 Hshape Hpc H1 H6)
 as[b[c[time[last[HR[HT[HN[HP[HL1[HL6 HF]]]]]]]]]].
 exists b,c,time,last;split;[apply p230_instruction_history_correct;exact HR|].
 split;[exact HT|]. split;[exact HN|]. split;[exact HP|].
 apply(p230_ax_register_graph_update M env symbolic start last 1(program230_register symbolic r)(program230_register start r));
 [exact HG|exact(HG r Hr)|exact HL1|].
 intros j Hj Hj1;destruct(Nat.eq_dec j 6)as[->|Hj6];[now rewrite HL6,H6|exact(HF j Hj Hj1 Hj6)].
Qed.
Theorem p230_ax_native_load_runtime M env before after start P r:
 (r<9)%nat->r<>1->r<>6->program230_parameter_shape P r->
 program230_pc start=program230_path_value M P->program230_register start 6=zeroM M->
 p230_ax_register_graph M env before start->program230_register before 1=CEconst 0->
 p230_ax_native_step(ANLoad r)before=Some after->
 p230_ax_runtime_result M env after start(inc_path(P++[true])).
Proof.
 intros Hr Hr1 Hr6 Hshape HP H6 HG Htop HS.
 change(match program230_register before 1 with CEconst 0=>Some(p230_ax_set before 1(program230_register before r))|_=>None end=Some after)in HS.
 rewrite Htop in HS;injection HS as <-.
 apply(p230_ax_parameter_runtime M env before start P r Hr Hr1 Hr6 Hshape HP);[|exact H6|exact HG].
 pose proof(HG 1 ltac:(lia))as H1;rewrite Htop in H1;exact H1.
Qed.
Theorem p230_ax_unpair_runtime M env symbolic start P n ix iy:
 In(P,8,n)p230_unpair_sites->program230_pc start=program230_path_value M P->
 program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 p230_ax_register_graph M env symbolic start->
 pair_graph M(env ix)(env iy)(program230_register start 8)->
 p230_ax_runtime_result M env
 (p230_ax_set(p230_ax_set(p230_ax_set symbolic 8(CEconst 0))6(CEvar ix))7(CEvar iy))start(inc_path P).
Proof.
 intros Hsite HP H6 H7 HG Hpair.
 destruct(p230_unpair_site_history M P 8 n start(program230_register start 8)Hsite HP eq_refl H6 H7)
 as[b[c[time[last[HR[HT[HN[Hpc[H8[Hdecoded HF]]]]]]]]]].
 destruct(pair_injective M(program230_register start 8)(program230_register last 6)(program230_register last 7)
 (env ix)(env iy)Hdecoded Hpair)as[HX HY].
 set(canonical:=p230_ax_actual_set M(p230_ax_actual_set M(p230_ax_actual_set M start 8(zeroM M)(program230_path_value M(inc_path P)))
 6(env ix)(program230_path_value M(inc_path P)))7(env iy)(program230_path_value M(inc_path P))).
 assert(EL:last=canonical).
 {apply program230_configuration_ext;intros j Hj;destruct j as[|i];[exact Hpc|].
  change(program230_register last i=program230_register canonical i).
  unfold canonical;rewrite !p230_ax_actual_set_register by lia.
  destruct(Nat.eqb i 7)eqn:E7;[apply Nat.eqb_eq in E7;subst i;exact HY|].
  destruct(Nat.eqb i 6)eqn:E6;[apply Nat.eqb_eq in E6;subst i;exact HX|].
  destruct(Nat.eqb i 8)eqn:E8;[apply Nat.eqb_eq in E8;subst i;exact H8|].
  apply HF;[lia|now apply Nat.eqb_neq|now apply Nat.eqb_neq|now apply Nat.eqb_neq]. }
 exists b,c,time,last;split;[apply p230_instruction_history_correct;exact HR|].
 split;[exact HT|]. split;[exact HN|]. split;[exact Hpc|].
 rewrite EL;apply(p230_ax_graph_unpair M env symbolic start(env ix)(env iy)ix iy _ HG eq_refl eq_refl).
Qed.
Theorem p230_ax_native_unpair_runtime M env before after start P n:
 In(P,8,n)p230_unpair_sites->program230_pc start=program230_path_value M P->
 program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 p230_ax_register_graph M env before start->
 (program230_register before 8=CEvar 8 \/program230_register before 8=CEvar 9)->
 pair_graph M(env 11)(env 9)(env 8)->pair_graph M(env 4)(env 10)(env 9)->
 p230_ax_native_step ANUnpair before=Some after->p230_ax_runtime_result M env after start(inc_path P).
Proof.
 intros Hsite HP H6 H7 HG Hform HP8 HP9 HS;destruct Hform as[HE|HE].
 -change(match program230_register before 8 with
  |CEvar 8=>Some(p230_ax_set(p230_ax_set(p230_ax_set before 8(CEconst 0))6(CEvar 11))7(CEvar 9))
  |CEvar 9=>Some(p230_ax_set(p230_ax_set(p230_ax_set before 8(CEconst 0))6(CEvar 4))7(CEvar 10))|_=>None end=Some after)in HS.
  rewrite HE in HS;injection HS as <-.
  apply(p230_ax_unpair_runtime M env before start P n 11 9 Hsite HP H6 H7 HG).
  pose proof(HG 8 ltac:(lia))as H8;rewrite HE in H8;change(program230_register start 8=env 8)in H8;now rewrite H8.
 -change(match program230_register before 8 with
  |CEvar 8=>Some(p230_ax_set(p230_ax_set(p230_ax_set before 8(CEconst 0))6(CEvar 11))7(CEvar 9))
  |CEvar 9=>Some(p230_ax_set(p230_ax_set(p230_ax_set before 8(CEconst 0))6(CEvar 4))7(CEvar 10))|_=>None end=Some after)in HS.
  rewrite HE in HS;injection HS as <-.
  apply(p230_ax_unpair_runtime M env before start P n 4 10 Hsite HP H6 H7 HG).
  pose proof(HG 8 ltac:(lia))as H8;rewrite HE in H8;change(program230_register start 8=env 9)in H8;now rewrite H8.
Qed.
Print Assumptions p230_ax_parameter_runtime.
Print Assumptions p230_ax_native_load_runtime.
Print Assumptions p230_ax_unpair_runtime.
Print Assumptions p230_ax_native_unpair_runtime.
