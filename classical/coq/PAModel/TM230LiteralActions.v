(** Exact finite action list read from the published e7ccbcec... transition table. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import Table230 TM230.
Import ListNotations.
Module Public230 := K230.TM230.
Definition machine230_action:Type :=(nat*bool*bool*dir*nat)%type.
Definition machine230_actions_at(q:nat):list machine230_action :=
 match nth_error table230 q with
 |None=>[]
 |Some(w0,d0,n0,w1,d1,n1)=>[(q,false,w0,d0,n0);(q,true,w1,d1,n1)]
 end.
Definition machine230_actions:list machine230_action :=
 flat_map machine230_actions_at(seq 0 Public230.NH).
Theorem machine230_action_exact q b w d n:
 In(q,b,w,d,n)machine230_actions <->Public230.tmn q b=Some(w,d,n).
Proof.
 unfold machine230_actions. split.
 -intro H. apply in_flat_map in H as(q0&Hq0&Hrow).
  unfold machine230_actions_at in Hrow.
  destruct(nth_error table230 q0)as[row|]eqn:E;[|contradiction].
  destruct row as [[[[[w0 d0]n0]w1]d1]n1].
  simpl in Hrow. destruct Hrow as[H|[H|H]];[| |contradiction];
  inversion H;subst;unfold Public230.tmn;rewrite E;reflexivity.
 -intro H. unfold Public230.tmn in H.
  destruct(nth_error table230 q)as[row|]eqn:E;[|discriminate].
  destruct row as [[[[[w0 d0]n0]w1]d1]n1].
  assert(Hq:q<Public230.NH).
  {rewrite <-Public230.table_length. apply nth_error_Some. rewrite E. discriminate. }
  apply in_flat_map. exists q. split;[apply in_seq;lia|].
  unfold machine230_actions_at. rewrite E. destruct b;inversion H;subst;simpl;auto.
Qed.
Theorem machine230_action_count:length machine230_actions=460.
Proof. reflexivity. Qed.
Definition machine230_bit(b:bool):nat :=if b then 1 else 0.
Definition machine230_direction(d:dir):nat :=match d with L=>0|R=>1 end.
Lemma machine230_bit_injective a b:machine230_bit a=machine230_bit b->a=b.
Proof. destruct a,b;cbn;congruence. Qed.
Lemma machine230_direction_injective a b:machine230_direction a=machine230_direction b->a=b.
Proof. destruct a,b;cbn;congruence. Qed.
Print Assumptions machine230_action_exact.
Print Assumptions machine230_action_count.
