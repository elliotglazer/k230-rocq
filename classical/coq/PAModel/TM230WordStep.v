(** Exact one-step calibration with finite tapes in the published BusyCoq semantics. *)
From PAModel Require Import TM230LiteralActions TM230TransitionArithmetic TM230BinaryStep StandardModel.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Zip TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint machine230_word_value(xs:list bool):nat:=
 match xs with[]=>0|x::xs=>machine230_bit x+2*machine230_word_value xs end.
Lemma machine230_word_split xs:
 machine230_word_value xs=machine230_bit(hd false xs)+2*machine230_word_value(tl xs).
Proof. destruct xs;reflexivity. Qed.
Definition machine230_word_config(q:nat)(l:list bool)(h:bool)(r:list bool):machine230_config nat:=
 machine230_mk_config nat q(machine230_word_value l)(machine230_bit h)(machine230_word_value r).
Theorem machine230_word_right q l h r w n:
 Public230.tmn q h=Some(w,TM.R,n)->
 machine230_step natModel(machine230_word_config q l h r)
 (machine230_word_config n(w::l)(hd false r)(tl r)).
Proof.
 intro H. unfold machine230_step,machine230_word_config;cbn[machine230_state machine230_left machine230_head machine230_right].
 exists(machine230_bit w),(machine230_direction TM.R). split.
 -now apply(proj2(machine230_transition_nat_exact q h w TM.R n)).
 -split.
  +destruct(hd false r);[right|left];reflexivity.
  +right. change(1=1 /\machine230_word_value(w::l)=2*machine230_word_value l+machine230_bit w /\
    machine230_word_value r=2*machine230_word_value(tl r)+machine230_bit(hd false r)).
   pose proof(machine230_word_split r)as HS. cbn[machine230_word_value]. repeat split;lia.
Qed.
Theorem machine230_word_left q l h r w n:
 Public230.tmn q h=Some(w,TM.L,n)->
 machine230_step natModel(machine230_word_config q l h r)
 (machine230_word_config n(tl l)(hd false l)(w::r)).
Proof.
 intro H. unfold machine230_step,machine230_word_config;cbn[machine230_state machine230_left machine230_head machine230_right].
 exists(machine230_bit w),(machine230_direction TM.L). split.
 -now apply(proj2(machine230_transition_nat_exact q h w TM.L n)).
 -split.
  +destruct(hd false l);[right|left];reflexivity.
  +left. change(0=0 /\machine230_word_value(w::r)=2*machine230_word_value r+machine230_bit w /\
    machine230_word_value l=2*machine230_word_value(tl l)+machine230_bit(hd false l)).
   pose proof(machine230_word_split l)as HS. cbn[machine230_word_value]. repeat split;lia.
Qed.
Theorem machine230_word_right_public q l h r w n:
 Public230.tmn q h=Some(w,TM.R,n)->
 Public230.TM230.step Public230.tm
 (K230.Zip.zc(Public230.st q)l(h::r))
 (K230.Zip.zc(Public230.st n)(w::l)r).
Proof. intro H. apply K230.Zip.zR. now apply Public230.tm_st. Qed.
Theorem machine230_word_left_public q l h r w n:
 Public230.tmn q h=Some(w,TM.L,n)->
 Public230.TM230.step Public230.tm
 (K230.Zip.zc(Public230.st q)l(h::r))
 (K230.Zip.zl(Public230.st n)l(w::r)).
Proof. intro H. apply K230.Zip.zL. now apply Public230.tm_st. Qed.
Print Assumptions machine230_word_right.
Print Assumptions machine230_word_left.
Print Assumptions machine230_word_right_public.
Print Assumptions machine230_word_left_public.
