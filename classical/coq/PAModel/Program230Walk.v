(** Uniform finite control selection in an arbitrary PA model. The numeric PC
    may be nonstandard. The finite path witness is obtained from genuine
    implicit-zero reads, not from a standardness premise on the PC. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 NumericalProofs TM230LiteralActions TM230BitArithmetic Program230PathCode
 Program230PathPop Program230Read Program230Bounds.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition program230_walk M p code e Q rest:Prop:=
 program230_read M code Q rest /\
 fol p(ENode(root p))Q=Some e /\is_node e=false.

Lemma program230_read_app M P code Q rest:
 program230_read M code(P++Q)rest<->
 exists middle,program230_read M code P middle /\program230_read M middle Q rest.
Proof.
 induction P as[|b P IH]in code|-*;cbn[app program230_read].
 -split;[intro H;exists code;auto|intros[middle[-> H]];exact H].
 -split.
  +intros[next[Hp Hr]]. apply IH in Hr as[middle[H1 H2]].
   exists middle;split;[exists next;auto|exact H2].
  +intros[middle[[next[Hp H1]]H2]]. exists next;split;[exact Hp|].
   apply IH;exists middle;auto.
Qed.
Lemma program230_read_firstn M code bits rest n:
 program230_read M code bits rest->exists middle,program230_read M code(firstn n bits)middle.
Proof.
 intro H. rewrite <-(firstn_skipn n bits)in H.
 apply program230_read_app in H as[middle[H1 H2]];eauto.
Qed.
Lemma program230_take_zeros_firstn n P:
 (n<=length P)%nat->program230_take_zeros n P=firstn n P.
Proof.
 intro H. rewrite program230_take_zeros_source_prefix,firstn_app.
 replace(n-length P)%nat with 0%nat by lia;cbn;apply app_nil_r.
Qed.
Lemma program230_source_walk_bound p fuel n P i e d:
 walk p fuel n P i = Some(e,d)->(d<=i+fuel)%nat.
Proof.
 induction fuel as[|fuel IH]in n,i|-*;intro H;[discriminate|].
 rewrite walk_S in H.
 destruct(child p n(bit P i))as[m|r|r|k|k|];
  try(injection H as <- <-;lia).
 specialize(IH m(S i)H);lia.
Qed.

Theorem program230_walk_source M p fuel P e d:
 walk p fuel(root p)P 0=Some(e,d)->
 program230_walk M p(program230_path_value M P)e(program230_take_zeros d P)
  (program230_path_value M(skipn d P)).
Proof.
 intro H. unfold program230_walk;split;[apply program230_read_path|].
 split.
 -rewrite program230_take_zeros_source_prefix,pad_bits.
  pose proof(walk_fol p fuel(root p)P 0 e d H)as HF.
  now rewrite Nat.sub_0_r in HF.
 -exact(proj2(walk_gt p fuel(root p)P 0 e d H)).
Qed.

Lemma program230_fol_read_deterministic M p Q a code e rest Q' e' rest':
 fol p a Q=Some e->is_node e=false->program230_read M code Q rest->
 fol p a Q'=Some e'->is_node e'=false->program230_read M code Q' rest'->
 Q=Q' /\e=e' /\rest=rest'.
Proof.
 induction Q as[|b Q IH]in a,code,e,rest,Q',e',rest'|-*;
  destruct Q' as[|b' Q'];cbn[fol program230_read];intros HF HL HR KF KL KR.
 -injection HF as <-. injection KF as <-. split;[reflexivity|split;[reflexivity|congruence]].
 -injection HF as <-. destruct a;try discriminate HL;discriminate KF.
 -injection KF as <-. destruct a;try discriminate KL;discriminate HF.
 -destruct a as[n|r|r|k|k|];try discriminate HF.
  destruct HR as[next[HP HR]],KR as[next'[KP KR]].
  destruct(program230_path_pop_unique M code(machine230_bitM M b)next
   (machine230_bitM M b')next' HP KP)as[HB Hnext].
  apply program230_bitM_injective in HB;subst b' next'.
  destruct(IH(child p n b)next e rest Q' e' rest' HF HL HR KF KL KR)as[HQ[HE HRr]].
  subst Q';split;[reflexivity|auto].
Qed.
Theorem program230_walk_deterministic M p code e Q rest e' Q' rest':
 program230_walk M p code e Q rest->program230_walk M p code e' Q' rest'->
 Q=Q' /\e=e' /\rest=rest'.
Proof.
 intros[HR[HF HL]][KR[KF KL]].
 exact(program230_fol_read_deterministic M p Q(ENode(root p))code e rest Q' e' rest'
  HF HL HR KF KL KR).
Qed.

Theorem program230_walk_total M p code:
 wf p->code<>zeroM M->exists e Q rest,
 program230_walk M p code e Q rest /\(length Q<=nnodes p+1)%nat.
Proof.
 intros W Hnz.
 destruct(program230_read_total M(nnodes p+1)code Hnz)as[bits[rest[Hlen[HR Hrest]]]].
 destruct(wf_walk p W bits)as[e[d HW]].
 pose proof(program230_source_walk_bound p(nnodes p+1)(root p)bits 0 e d HW)as HD.
 assert(HD':(d<=length bits)%nat)by lia.
 destruct(program230_read_firstn M code bits rest d HR)as[middle HP].
 exists e,(program230_take_zeros d bits),middle;split.
 -unfold program230_walk;split.
  +rewrite(program230_take_zeros_firstn d bits HD');exact HP.
  +split.
   *rewrite program230_take_zeros_source_prefix,pad_bits.
    pose proof(walk_fol p(nnodes p+1)(root p)bits 0 e d HW)as HF.
    now rewrite Nat.sub_0_r in HF.
   *exact(proj2(walk_gt p(nnodes p+1)(root p)bits 0 e d HW)).
 -rewrite program230_take_zeros_length;lia.
Qed.

Theorem program230_walk_source_exact M p P e Q rest:
 wf p->program230_walk M p(program230_path_value M P)e Q rest->
 walk p(nnodes p+1)(root p)P 0=Some(e,length Q) /\
 Q=firstn(length Q)(P++repeat false(length Q)) /\
 rest=program230_path_value M(skipn(length Q)P).
Proof.
 intros W H. destruct(wf_walk p W P)as[e0[d HW]].
 pose proof(program230_walk_source M p(nnodes p+1)P e0 d HW)as HK.
 destruct(program230_walk_deterministic M p(program230_path_value M P)e Q rest
   e0(program230_take_zeros d P)(program230_path_value M(skipn d P))H HK)as[-> [-> ->]].
 rewrite program230_take_zeros_length. split;[exact HW|split;[apply program230_take_zeros_source_prefix|reflexivity]].
Qed.

Theorem program230_walk_p230_register_supported M code e Q rest:
 program230_walk M p230 code e Q rest->program230_edge_register_supported e.
Proof.
 intros[HR[HF HL]].
 pose proof(walk_leaf p230 p230_wf Q e Q HF HL(fun i => eq_refl))as HW.
 exact(program230_root_register_supported Q e(length Q)HW).
Qed.

Print Assumptions program230_walk_source.
Print Assumptions program230_walk_deterministic.
Print Assumptions program230_walk_total.
Print Assumptions program230_walk_source_exact.
Print Assumptions program230_walk_p230_register_supported.
