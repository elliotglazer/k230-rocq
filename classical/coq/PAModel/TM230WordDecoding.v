(** Reverse one-step calibration, including binary-pop uniqueness. *)
From PAModel Require Import TM230LiteralActions TM230TransitionArithmetic TM230BinaryStep TM230WordStep StandardModel.
From K230 Require Zip TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma machine230_bit_cases b:machine230_bit b=0 \/machine230_bit b=1.
Proof. destruct b;cbn;auto. Qed.
Lemma machine230_pop_unique a b c d:
 2*a+b=2*c+d->(b=0\/b=1)->(d=0\/d=1)->a=c/\b=d.
Proof. intros H Hb Hd. destruct Hb,Hd;lia. Qed.
Lemma machine230_zc_default q l r:
 K230.Zip.zc q l(hd false r::tl r)=K230.Zip.zc q l r.
Proof. destruct r;reflexivity. Qed.
Theorem machine230_word_step_complete q l h r t:
 machine230_step natModel(machine230_word_config q l h r)t->
 exists n l' h' r',t=machine230_word_config n l' h' r' /\
 Public230.TM230.step Public230.tm
 (K230.Zip.zc(Public230.st q)l(h::r))
 (K230.Zip.zc(Public230.st n)l'(h'::r')).
Proof.
 destruct t as[qt lt ht rt].
 unfold machine230_step,machine230_word_config.
 cbn[machine230_state machine230_left machine230_head machine230_right].
 intros(w&d&HT&Hbit&Hmove).
 destruct HT as(a&HA&HE). destruct a as[[[[qa ba]wa]da]na].
 unfold machine230_action_relation in HE. rewrite !numeral_natModel in HE.
 destruct HE as(Hq&Hh&Hw&Hd&Hn).
 apply machine230_bit_injective in Hh. subst qa ba w d qt.
 assert(Htable:Public230.tmn q h=Some(wa,da,na))by(now apply(proj1(machine230_action_exact q h wa da na))).
 change(ht=0\/ht=1)in Hbit.
 destruct da.
 -destruct Hmove as[(HD&HR&HL)|(HD&HL&HR)];[|discriminate HD].
  change(rt=2*machine230_word_value r+machine230_bit wa)in HR.
  change(machine230_word_value l=2*lt+ht)in HL.
  pose proof(machine230_word_split l)as HS.
  assert(EP:lt=machine230_word_value(tl l)/\ht=machine230_bit(hd false l)).
  {apply machine230_pop_unique;[lia|exact Hbit|apply machine230_bit_cases]. }
  destruct EP as[-> ->].
  exists na,(tl l),(hd false l),(wa::r). split.
  +unfold machine230_word_config. cbn[machine230_word_value]. f_equal;lia.
  +change(Public230.TM230.step Public230.tm
    (K230.Zip.zc(Public230.st q)l(h::r))(K230.Zip.zl(Public230.st na)l(wa::r))).
   now apply machine230_word_left_public.
 -destruct Hmove as[(HD&HR&HL)|(HD&HL&HR)];[discriminate HD|].
  change(lt=2*machine230_word_value l+machine230_bit wa)in HL.
  change(machine230_word_value r=2*rt+ht)in HR.
  pose proof(machine230_word_split r)as HS.
  assert(EP:rt=machine230_word_value(tl r)/\ht=machine230_bit(hd false r)).
  {apply machine230_pop_unique;[lia|exact Hbit|apply machine230_bit_cases]. }
  destruct EP as[-> ->].
  exists na,(wa::l),(hd false r),(tl r). split.
  +unfold machine230_word_config. cbn[machine230_word_value]. f_equal;lia.
  +rewrite machine230_zc_default. now apply machine230_word_right_public.
Qed.
Print Assumptions machine230_word_step_complete.
