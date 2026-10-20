(** Exact finite-control bounds and the unique terminal state of the public table. *)
From PAModel Require Import TM230LiteralActions.
From K230 Require Table230 TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_action_bounds(a:machine230_action):bool:=
 let '(q,r,w,d,n):=a in Nat.ltb q 230&&Nat.leb n 230.
Lemma machine230_checked_action_bounds:forallb machine230_action_bounds machine230_actions=true.
Proof. vm_compute. reflexivity. Qed.
Theorem machine230_transition_bounds q r w d n:
 Public230.tmn q r=Some(w,d,n)->q<230/\n<=230.
Proof.
 intro H. apply(proj2(machine230_action_exact q r w d n))in H.
 pose proof(proj1(forallb_forall machine230_action_bounds machine230_actions)machine230_checked_action_bounds(q,r,w,d,n)H)as B.
 unfold machine230_action_bounds in B. apply andb_true_iff in B as[Bq Bn].
 apply Nat.ltb_lt in Bq. apply Nat.leb_le in Bn. auto.
Qed.
Theorem machine230_nonterminal_total q r:
 q<230->exists w d n,Public230.tmn q r=Some(w,d,n)/\n<=230.
Proof.
 intro Hq. unfold Public230.tmn.
 destruct(List.nth_error Table230.table230 q)as[row|]eqn:E.
 -destruct row as[[[[[w0 d0]n0]w1]d1]n1]. destruct r.
  +exists w1,d1,n1. split;[reflexivity|].
   exact(proj2(machine230_transition_bounds q true w1 d1 n1 ltac:(unfold Public230.tmn;now rewrite E))).
  +exists w0,d0,n0. split;[reflexivity|].
   exact(proj2(machine230_transition_bounds q false w0 d0 n0 ltac:(unfold Public230.tmn;now rewrite E))).
 -apply nth_error_None in E. change(230<=q)in E. lia.
Qed.
Theorem machine230_terminal_exact q r:
 q<=230->(Public230.tmn q r=None<->q=230).
Proof.
 intro Hq. split.
 -intro H. destruct(Nat.lt_ge_cases q 230)as[Hlt|Hge];[|lia].
  destruct(machine230_nonterminal_total q r Hlt)as(w&d&n&E&HN). rewrite E in H. discriminate.
 -intro E. subst q. destruct r;reflexivity.
Qed.
Print Assumptions machine230_transition_bounds.
Print Assumptions machine230_nonterminal_total.
Print Assumptions machine230_terminal_exact.
