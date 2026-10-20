(** Real arithmetic paths for all non-box actions of the pinned runtime. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230Paths TM230SymbolicSegments TM230SymbolicCells TM230RuntimeWords.
From K230 Require Runtime230Core TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section Actions.
Variable M:Model.
Variable gap:carrier M.
Variable Box:Runtime230.boxst->carrier M->Prop.
Local Notation Z:=(zeroM M).
Local Notation two:=(succM M(succM M Z)).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_runtime_action_ring:(model_semiring M).
Theorem machine230_runtime_reorient q b ls rs s:
 machine230_runtime_view M gap Box(q,true,Runtime230.SB b::ls,rs)s ->
 machine230_runtime_view M gap Box(q,false,ls,Runtime230.SB b::rs)s.
Proof.
 intros[l[r[[rest[Hl Hcell]][Hr Hs]]]]. apply machine230_cell_value in Hcell. subst l.
 exists rest,(machine230_bitM M b+two*r). split;[exact Hl|]. split.
 -exists r;split;[exact Hr|apply machine230_cell_value;reflexivity].
 -exact(proj1(machine230_views_reorient M q b rest r s)Hs).
Qed.
Theorem machine230_runtime_reorient_blank q rs s:
 machine230_runtime_view M gap Box(q,true,[],rs)s ->
 machine230_runtime_view M gap Box(q,false,[],Runtime230.SB false::rs)s.
Proof.
 intros[l[r[Hl[Hr Hs]]]]. change(l=Z)in Hl. subst l.
 assert(E:Z=machine230_bitM M false+two*Z)by(change(Z=Z+two*Z);ring).
 rewrite E in Hs at 1.
 exists Z,(machine230_bitM M false+two*r). split;[reflexivity|]. split.
 -exists r;split;[exact Hr|apply machine230_cell_value;reflexivity].
 -exact(proj1(machine230_views_reorient M q false Z r s)Hs).
Qed.
Theorem machine230_runtime_cell_right q b w q' ls rs s:
 Public230.tmn q b=Some(w,TM.R,q')->
 machine230_runtime_view M gap Box(q,false,ls,Runtime230.SB b::rs)s ->
 exists t,machine230_runtime_view M gap Box(q',false,Runtime230.SB w::ls,rs)t /\machine230_step M s t.
Proof.
 intros Htable[l[r[Hl[[rest[Hr Hcell]]Hs]]]]. apply machine230_cell_value in Hcell. subst r.
 destruct(machine230_right_view_total M q'(two*l+machine230_bitM M w)rest)as[t Ht].
 exists t. split.
 -exists(two*l+machine230_bitM M w),rest. split.
  +exists l;split;[exact Hl|apply machine230_cell_value;ring].
  +split;assumption.
 -exact(machine230_right_view_step M q b w q' l rest s t Htable Hs Ht).
Qed.
Theorem machine230_runtime_cell_left q b w q' ls rs s:
 Public230.tmn q b=Some(w,TM.L,q')->
 machine230_runtime_view M gap Box(q,false,ls,Runtime230.SB b::rs)s ->
 exists t,machine230_runtime_view M gap Box(q',true,ls,Runtime230.SB w::rs)t /\machine230_step M s t.
Proof.
 intros Htable[l[r[Hl[[rest[Hr Hcell]]Hs]]]]. apply machine230_cell_value in Hcell. subst r.
 destruct(machine230_left_view_total M q'(machine230_bitM M w+two*rest)l)as[t Ht].
 exists t. split.
 -exists l,(machine230_bitM M w+two*rest). split;[exact Hl|]. split.
  +exists rest;split;[exact Hr|apply machine230_cell_value;reflexivity].
  +exact Ht.
 -exact(machine230_right_to_left_step M q b w q' l rest s t Htable Hs Ht).
Qed.
Theorem machine230_runtime_scan_right q b w a c ls rs s:
 Public230.tmn q b=Some(w,TM.R,q)->
 machine230_runtime_view M gap Box(q,false,ls,Runtime230.SR b a c::rs)s ->
 exists t,machine230_runtime_view M gap Box(q,false,Runtime230.SR w a c::ls,rs)t /\machine230_reaches M s t.
Proof.
 intros Htable[l[r[Hl[[rest[Hr Hprefix]]Hs]]]].
 assert(Hsymbol:machine230_symbolic_view M gap q false [] [machine230_make_segment b a c]l rest s).
 {exists l,r;split;[reflexivity|]. split;[exists rest;split;[reflexivity|exact Hprefix]|exact Hs]. }
 destruct(machine230_symbolic_scan_right M gap q b w a c [] [] l rest s Htable Hsymbol)as[t[Htarget HP]].
 destruct Htarget as[out[r'[[base[Hbase Hout]][Hr' Ht]]]].
 change(base=l)in Hbase. change(r'=rest)in Hr'. subst base r'.
 exists t. split;[|exact HP]. exists out,rest. split;[exists l;auto|auto].
Qed.
Theorem machine230_runtime_scan_left q b w a c ls rs s:
 Public230.tmn q b=Some(w,TM.L,q)->
 machine230_runtime_view M gap Box(q,true,Runtime230.SR b a c::ls,rs)s ->
 exists t,machine230_runtime_view M gap Box(q,true,ls,Runtime230.SR w a c::rs)t /\machine230_reaches M s t.
Proof.
 intros Htable[l[r[[rest[Hl Hprefix]][Hr Hs]]]].
 assert(Hsymbol:machine230_symbolic_view M gap q true [machine230_make_segment b a c] [] rest r s).
 {exists l,r;split;[exists rest;split;[reflexivity|exact Hprefix]|]. split;[reflexivity|exact Hs]. }
 destruct(machine230_symbolic_scan_left M gap q b w a c [] [] rest r s Htable Hsymbol)as[t[Htarget HP]].
 destruct Htarget as[l'[out[Hl'[[base[Hbase Hout]]Ht]]]].
 change(l'=rest)in Hl'. change(base=r)in Hbase. subst l' base.
 exists t. split;[|exact HP]. exists rest,out. split;[exact Hl|]. split;[exists r;auto|exact Ht].
Qed.
End Actions.
Print Assumptions machine230_runtime_reorient.
Print Assumptions machine230_runtime_reorient_blank.
Print Assumptions machine230_runtime_cell_right.
Print Assumptions machine230_runtime_cell_left.
Print Assumptions machine230_runtime_scan_right.
Print Assumptions machine230_runtime_scan_left.

