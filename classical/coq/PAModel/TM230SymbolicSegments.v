(** The homogeneous SB/SR part of the public symbolic executor, interpreted
    using arithmetic words and actual internally coded machine paths. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230Paths TM230RunPrefixes TM230ScanRight TM230ScanLeft PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Record machine230_segment := machine230_make_segment {
 machine230_segment_bit:bool;machine230_segment_factor:nat;machine230_segment_constant:nat}.
Definition machine230_segment_length M gap s:=
 addM M(mulM M(code_numeral M(machine230_segment_factor s))gap)
 (code_numeral M(machine230_segment_constant s)).
Definition machine230_segment_value M gap s tail word:=
 machine230_run_prefix M(machine230_segment_bit s)(machine230_segment_length M gap s)tail word.
Fixpoint machine230_segments_value M gap (ss:list machine230_segment) tail word:Prop:=
 match ss with
 |[]=>word=tail
 |s::ss=>exists middle,machine230_segments_value M gap ss tail middle /\
 machine230_segment_value M gap s middle word
 end.
Definition machine230_symbolic_view M gap q(onleft:bool)ls rs ltail rtail s:=
 exists l r,machine230_segments_value M gap ls ltail l /\
 machine230_segments_value M gap rs rtail r /\
 if onleft then machine230_left_view M q r l s else machine230_right_view M q l r s.
Theorem machine230_segments_total M gap ss tail:
 exists word,machine230_segments_value M gap ss tail word.
Proof.
 induction ss as[|s ss[middle Hmiddle]];[exists tail;reflexivity|].
 destruct(machine230_run_prefix_total M(machine230_segment_bit s)(machine230_segment_length M gap s)middle)as[word Hword].
 exists word,middle. auto.
Qed.
Theorem machine230_segments_functional M gap ss tail x y:
 machine230_segments_value M gap ss tail x->machine230_segments_value M gap ss tail y->x=y.
Proof.
 revert x y. induction ss as[|s ss IH];intros x y Hx Hy;[cbn in Hx,Hy;congruence|].
 destruct Hx as[a[Ha Hx]],Hy as[b[Hb Hy]].
 assert(E:a=b)by(exact(IH a b Ha Hb)). subst b.
 exact(machine230_run_prefix_functional M(machine230_segment_bit s)(machine230_segment_length M gap s)a x y Hx Hy).
Qed.
Theorem machine230_segments_append M gap xs ys tail word:
 machine230_segments_value M gap(xs++ys)tail word <->
 exists middle,machine230_segments_value M gap ys tail middle /\machine230_segments_value M gap xs middle word.
Proof.
 revert word. induction xs as[|s xs IH];intro word;cbn.
 -split;[intro H;exists word;auto|intros[x[H ->]];exact H].
 -setoid_rewrite IH. split.
  +intros[x[[y[Hy Hx]]Hhead]]. exists y. split;[exact Hy|]. exists x;auto.
  +intros[y[Hy[x[Hx Hhead]]]]. exists x. split;[exists y;auto|exact Hhead].
Qed.
Theorem machine230_symbolic_view_total M gap q onleft ls rs ltail rtail:
 exists s,machine230_symbolic_view M gap q onleft ls rs ltail rtail s.
Proof.
 destruct(machine230_segments_total M gap ls ltail)as[l Hl].
 destruct(machine230_segments_total M gap rs rtail)as[r Hr].
 destruct onleft.
 -destruct(machine230_left_view_total M q r l)as[s Hs]. exists s,l,r. auto.
 -destruct(machine230_right_view_total M q l r)as[s Hs]. exists s,l,r. auto.
Qed.
Section Scans.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation two:=(succM M(succM M Z)).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_symbolic_ring:(model_semiring M).
Theorem machine230_symbolic_scan_right gap q b w a c ls rs ltail rtail s:
 Public230.tmn q b=Some(w,TM.R,q)->
 machine230_symbolic_view M gap q false ls(machine230_make_segment b a c::rs)ltail rtail s ->
 exists t,machine230_symbolic_view M gap q false(machine230_make_segment w a c::ls)rs ltail rtail t /\
 machine230_reaches M s t.
Proof.
 intros Htable[l[r[Hl[[rest[Hr Hprefix]]Hs]]]].
 destruct Hprefix as[p[k[Hp[Hpk Hword]]]]. change(r=k*machine230_bitM M b+p*rest)in Hword.
 set(out:=p*l+k*machine230_bitM M w).
 destruct(machine230_right_view_total M q out rest)as[t Ht].
 exists t. split.
 -exists out,rest. split;[exists l;split;[exact Hl|]|].
  +exists p,k. split;[exact Hp|]. split;[exact Hpk|]. change(out=k*machine230_bitM M w+p*l). unfold out;ring.
  +split;[exact Hr|exact Ht].
 -destruct s as[sq sl sh sr],t as[tq tl th tr].
  unfold machine230_right_view in Hs,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs,Ht.
  destruct Hs as[Hsq[Hsl[Hsh Hsw]]],Ht as[Htq[Htl[Hth Htw]]].
  subst sq sl tq tl. apply(machine230_scan_right M q b w Htable _ p k l sh sr th tr Hp Hpk Hsh Hth).
  change(sh+two*sr=k*machine230_bitM M b+p*(th+two*tr)).
  rewrite Hword,Htw in Hsw. replace(sh+two*sr)with(two*sr+sh)by ring. rewrite <-Hsw. ring.
Qed.
Theorem machine230_symbolic_scan_left gap q b w a c ls rs ltail rtail s:
 Public230.tmn q b=Some(w,TM.L,q)->
 machine230_symbolic_view M gap q true(machine230_make_segment b a c::ls)rs ltail rtail s ->
 exists t,machine230_symbolic_view M gap q true ls(machine230_make_segment w a c::rs)ltail rtail t /\
 machine230_reaches M s t.
Proof.
 intros Htable[l[r[[rest[Hl Hprefix]][Hr Hs]]]].
 destruct Hprefix as[p[k[Hp[Hpk Hword]]]]. change(l=k*machine230_bitM M b+p*rest)in Hword.
 set(out:=p*r+k*machine230_bitM M w).
 destruct(machine230_left_view_total M q out rest)as[t Ht].
 exists t. split.
 -exists rest,out. split;[exact Hl|]. split;[exists r;split;[exact Hr|]|exact Ht].
  exists p,k. split;[exact Hp|]. split;[exact Hpk|]. change(out=k*machine230_bitM M w+p*r). unfold out;ring.
 -destruct s as[sq sl sh sr],t as[tq tl th tr].
  unfold machine230_left_view in Hs,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs,Ht.
  destruct Hs as[Hsq[Hsr[Hsh Hsw]]],Ht as[Htq[Htr[Hth Htw]]].
  subst sq sr tq tr. apply(machine230_scan_left M q b w Htable _ p k r sh sl th tl Hp Hpk Hsh Hth).
  change(sh+two*sl=k*machine230_bitM M b+p*(th+two*tl)).
  rewrite Hword,Htw in Hsw. replace(sh+two*sl)with(two*sl+sh)by ring. rewrite <-Hsw. ring.
Qed.
End Scans.
Print Assumptions machine230_symbolic_scan_right.
Print Assumptions machine230_symbolic_scan_left.
Print Assumptions machine230_segments_functional.
