(** Every literal finite halting run has a corresponding finite arithmetic step derivation. *)
From PAModel Require Import TM230LiteralActions TM230BinaryStep TM230TableBounds TM230WordStep TM230WordDecoding StandardModel.
From K230 Require Zip TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Inductive machine230_nat_steps:nat->machine230_config nat->machine230_config nat->Prop:=
 |machine230_nat_steps_zero s:machine230_nat_steps 0 s s
 |machine230_nat_steps_cons n s t u:machine230_step natModel s t->machine230_nat_steps n t u->machine230_nat_steps(S n)s u.
Definition machine230_word_tape(q:nat)(l:list bool)(h:bool)(r:list bool):=
 K230.Zip.zc(Public230.st q)l(h::r).
Lemma machine230_word_halted q l h r:
 q<=230->Public230.TM230.halted Public230.tm(machine230_word_tape q l h r)->q=230.
Proof.
 intros Hq Hhalt. change(Public230.tm(Public230.st q,h)=None)in Hhalt.
 unfold Public230.tm in Hhalt. rewrite Public230.bval_bmk in Hhalt by exact Hq.
 apply(proj1(machine230_terminal_exact q h Hq)).
 destruct(Public230.tmn q h)as[[[w d]n]|]eqn:E;[discriminate Hhalt|reflexivity].
Qed.
Theorem machine230_public_termination_steps n q l h r:
 q<=230->Public230.TM230.halts_in Public230.tm(machine230_word_tape q l h r)n->
 exists t,machine230_nat_steps n(machine230_word_config q l h r)t/\machine230_state t=230.
Proof.
 revert q l h r. induction n as[|n IH];intros q l h r Hq(endc&Hmulti&Hhalt).
 -inversion Hmulti;subst. exists(machine230_word_config q l h r). split;[constructor|].
  cbn. now apply(machine230_word_halted q l h r Hq).
 -inversion Hmulti as[|n0 c0 mid lastc Hfirst Hrest];subst.
  assert(Hlt:q<230).
  {destruct(Nat.lt_ge_cases q 230)as[Hlt|Hge];[exact Hlt|].
   assert(E:q=230)by lia. subst q.
   exfalso. eapply Public230.TM230.halted_no_step;[|exact Hfirst].
   change(Public230.tm(Public230.st 230,h)=None). apply Public230.tm_halt. }
  destruct(machine230_nonterminal_total q h Hlt)as(w&d&next&HT&Hnext).
  destruct d.
  +pose proof(machine230_word_left_public q l h r w next HT)as HP.
   pose proof(Public230.TM230.step_deterministic Public230.tm _ _ _ Hfirst HP)as E.
   subst mid.
   assert(Htail:Public230.TM230.halts_in Public230.tm
    (machine230_word_tape next(tl l)(hd false l)(w::r))n).
   {exists endc. split;[exact Hrest|exact Hhalt]. }
   destruct(IH next(tl l)(hd false l)(w::r)Hnext Htail)as(t&Hsteps&Hstate).
   exists t. split;[|exact Hstate]. eapply machine230_nat_steps_cons with(t:=machine230_word_config next(tl l)(hd false l)(w::r));[exact(machine230_word_left q l h r w next HT)|exact Hsteps].
  +pose proof(machine230_word_right_public q l h r w next HT)as HP.
   pose proof(Public230.TM230.step_deterministic Public230.tm _ _ _ Hfirst HP)as E.
   subst mid.
   assert(Htail:Public230.TM230.halts_in Public230.tm
    (machine230_word_tape next(w::l)(hd false r)(tl r))n).
   {exists endc. split;[|exact Hhalt]. unfold machine230_word_tape. rewrite machine230_zc_default. exact Hrest. }
   destruct(IH next(w::l)(hd false r)(tl r)Hnext Htail)as(t&Hsteps&Hstate).
   exists t. split;[|exact Hstate]. eapply machine230_nat_steps_cons with(t:=machine230_word_config next(w::l)(hd false r)(tl r));[exact(machine230_word_right q l h r w next HT)|exact Hsteps].
Qed.
Print Assumptions machine230_public_termination_steps.
