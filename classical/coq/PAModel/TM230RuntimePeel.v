(** Literal peel actions preserve the actual arithmetic configuration. *)
From PAModel Require Import Model TM230RuntimeWords.
From K230 Require Runtime230Core.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem machine230_runtime_peel_left M gap Box q b a c ls rs conf moved s:
 Runtime230.peel_left q b a c ls rs=Some(conf,moved)->
 machine230_runtime_view M gap Box(q,true,Runtime230.SR b a c::ls,rs)s ->
 moved=false /\machine230_runtime_view M gap Box conf s.
Proof.
 unfold Runtime230.peel_left. destruct c as[|c];[destruct a as[|a]|];intro E;try discriminate;
 injection E as <- <-;intro Hs;split;[reflexivity| |reflexivity|].
 -destruct Hs as[l[r[Hl[Hr Hs]]]]. exists l,r. split;[|auto].
  exact(proj1(machine230_runtime_empty_run M gap Box b ls l)Hl).
 -destruct Hs as[l[r[Hl[Hr Hs]]]]. exists l,r. split;[|auto].
  exact(proj1(machine230_runtime_peel M gap Box b a c ls l)Hl).
Qed.
Theorem machine230_runtime_peel_right M gap Box q b a c ls rs conf moved s:
 Runtime230.peel_right q b a c ls rs=Some(conf,moved)->
 machine230_runtime_view M gap Box(q,false,ls,Runtime230.SR b a c::rs)s ->
 moved=false /\machine230_runtime_view M gap Box conf s.
Proof.
 unfold Runtime230.peel_right. destruct c as[|c];[destruct a as[|a]|];intro E;try discriminate;
 injection E as <- <-;intro Hs;split;[reflexivity| |reflexivity|].
 -destruct Hs as[l[r[Hl[Hr Hs]]]]. exists l,r. split;[exact Hl|]. split;[|exact Hs].
  exact(proj1(machine230_runtime_empty_run M gap Box b rs r)Hr).
 -destruct Hs as[l[r[Hl[Hr Hs]]]]. exists l,r. split;[exact Hl|]. split;[|exact Hs].
  exact(proj1(machine230_runtime_peel M gap Box b a c rs r)Hr).
Qed.
Print Assumptions machine230_runtime_peel_left.
Print Assumptions machine230_runtime_peel_right.
