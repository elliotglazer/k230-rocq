(** Finite control cleanliness for arithmetic public-program leaf steps.
    The auxiliary natural-register witness realizes only the selected branch;
    it is not a coding of the arbitrary-model arithmetic register tuple. *)
From PAModel Require Import Model Program230PathCode Program230Edges.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_inc_rev_length P:length(inc_rev P)=length P.
Proof. induction P as[|[|]P IH];cbn[inc_rev length];auto. Qed.
Lemma program230_inc_path_length P:length(inc_path P)=length P.
Proof. unfold inc_path;rewrite rev_length,program230_inc_rev_length,rev_length;reflexivity. Qed.
Lemma program230_strip_path_length b k P:(length(strip_path b k P)<=length P)%nat.
Proof. destruct(strip_path_prefix b k P)as[T E]. pose proof(f_equal(@length bool)E)as EL. rewrite length_app in EL;lia. Qed.
Lemma program230_brk_length k P:(length(brk k P)<=length P)%nat.
Proof. unfold brk;rewrite program230_inc_path_length;apply program230_strip_path_length. Qed.
Lemma program230_cont_length k P:(length(cont k P)<=length P)%nat.
Proof. apply program230_strip_path_length. Qed.
Lemma program230_read_prefix_length P d:length(firstn d(P++repeat false d))=d.
Proof. rewrite firstn_length,length_app,repeat_length. apply Nat.min_l;lia. Qed.

Theorem program230_edge_control_realized M p P Q e d R T pc':
 walk p(nnodes p+1)(root p)P 0=Some(e,d)->
 Q=firstn d(P++repeat false d)->program230_edge_step M Q e R T pc'->
 exists P' RN TN,pc'=program230_path_value M P' /\
 rm_step p(P,RN)=Some(P',TN) /\(length P'<=d)%nat.
Proof.
 intros HW HQ HE.
 assert(HL:length Q=d)by(rewrite HQ;apply program230_read_prefix_length).
 destruct e as[n|r|r|k|k|];cbn[program230_edge_step]in HE;try contradiction.
 -destruct HE as[Hr[Hpc HT]]. exists(inc_path Q),regs0,(upd regs0 r 1).
  split;[exact Hpc|]. split.
  +unfold rm_step;cbn[fst snd];rewrite HW;now rewrite <-HQ.
  +rewrite program230_inc_path_length,HL;lia.
 -destruct HE as[Hr[[H0[Hpc HT]]|[v[Hv[Hpc HT]]]]].
  +exists(brk 1 Q),regs0,regs0. split;[exact Hpc|]. split.
   *unfold rm_step;cbn[fst snd];rewrite HW;cbn[regs0];now rewrite <-HQ.
   *rewrite <-HL;apply program230_brk_length.
  +exists(inc_path Q),(fun _=>1),(upd(fun _=>1)r 0).
   split;[exact Hpc|]. split.
   *unfold rm_step;cbn[fst snd];rewrite HW;now rewrite <-HQ.
   *rewrite program230_inc_path_length,HL;lia.
 -destruct HE as[Hpc HT]. exists(brk k Q),regs0,regs0.
  split;[exact Hpc|]. split.
  +unfold rm_step;cbn[fst snd];rewrite HW;now rewrite <-HQ.
  +rewrite <-HL;apply program230_brk_length.
 -destruct HE as[Hpc HT]. exists(cont k Q),regs0,regs0.
  split;[exact Hpc|]. split.
  +unfold rm_step;cbn[fst snd];rewrite HW;now rewrite <-HQ.
  +rewrite <-HL;apply program230_cont_length.
Qed.

Theorem program230_edge_control_clean M p P Q e d R T pc':
 walk p(nnodes p+1)(root p)P 0=Some(e,d)->
 Q=firstn d(P++repeat false d)->program230_edge_step M Q e R T pc'->
 exists P',pc'=program230_path_value M P' /\clean p P' /\(length P'<=d)%nat.
Proof.
 intros HW HQ HE.
 destruct(program230_edge_control_realized M p P Q e d R T pc' HW HQ HE)as[P'[RN[TN[HC[HS HL]]]]].
 exists P'. split;[exact HC|]. split;[exact(step_clean p P RN P' TN HS)|exact HL].
Qed.
Corollary program230_edge_next_walk_bits M p P Q e d R T pc':
 walk p(nnodes p+1)(root p)P 0=Some(e,d)->
 Q=firstn d(P++repeat false d)->program230_edge_step M Q e R T pc'->
 exists P',pc'=program230_path_value M P' /\(length P'<=d)%nat /\
 forall next depth,walk p(nnodes p+1)(root p)P' 0=Some(next,depth)->
 forall i,(depth<=i)%nat->bit P' i=false.
Proof.
 intros HW HQ HE. destruct(program230_edge_control_clean M p P Q e d R T pc' HW HQ HE)
  as[P'[HC[Hclean HL]]]. exists P';auto.
Qed.
Print Assumptions program230_read_prefix_length.
Print Assumptions program230_edge_control_realized.
Print Assumptions program230_edge_control_clean.
Print Assumptions program230_edge_next_walk_bits.
