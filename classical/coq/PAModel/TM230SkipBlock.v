(** One literal skip-chain block, retaining its exact internal running time. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230Paths TM230ExactPaths TM230ScanRightExact TM230UnaryBlocks PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_skip_label j:=nth j[51;36;25;48;32;33;22;55;60]0.
Section Skip.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_skip_ring:(model_semiring M).
Theorem machine230_skip_one_block q q' value left tail word s:
 Public230.tmn q false=Some(false,TM.R,q')->
 Public230.tmn q' true=Some(true,TM.R,q')->
 machine230_unary_block M value tail word ->machine230_right_view M q left word s ->
 exists p k t,power2 M(S value)p /\p=S k /\
 machine230_right_view M q'(p*(two*left)+k)tail t /\
 machine230_reaches_in M(S(S value))s t.
Proof.
 intros Hzero Hones[p[k[Hp[Hpk Hword]]]]Hs.
 change(word=two*k+(two*p)*tail)in Hword.
 set(rest:=k+p*tail). set(midleft:=two*left).
 destruct(machine230_right_view_total M q' midleft rest)as[mid Hmid].
 destruct(machine230_right_view_total M q'(p*midleft+k)tail)as[t Ht].
 assert(Hfirst:machine230_step M s mid).
 {apply(machine230_right_view_step M q false false q' left rest _ _ Hzero).
  -change(machine230_right_view M q left(Z+two*rest)s).
   replace(Z+two*rest)with word;[exact Hs|]. rewrite Hword;unfold rest;ring.
  -change(machine230_right_view M q'(two*left+Z)rest mid).
   replace(two*left+Z)with midleft;[exact Hmid|unfold midleft;ring]. }
 assert(Hscan:machine230_reaches_in M(S value)mid t).
 {destruct mid as[mq ml mh mr],t as[tq tl th tr].
  unfold machine230_right_view in Hmid,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hmid,Ht.
  destruct Hmid as[Hmq[Hml[Hmh Hmw]]],Ht as[Htq[Htl[Hth Htw]]]. subst mq ml tq tl.
  replace(p*midleft+k)with(p*midleft+k*machine230_bitM M true)by(change(p*midleft+k*one=p*midleft+k);rewrite(succ_as_add M Z);ring).
  apply(machine230_scan_right_exact M q' true true Hones(S value)p k midleft mh mr th tr Hp Hpk Hmh Hth).
  change(mh+two*mr=k*one+p*(th+two*tr)).
  unfold rest in Hmw. rewrite Htw in Hmw. replace(mh+two*mr)with(two*mr+mh)by ring.
  rewrite <-Hmw,(succ_as_add M Z). ring. }
 exists p,k,t. split;[exact Hp|]. split;[exact Hpk|]. split;[exact Ht|].
 exact(machine230_reaches_in_step M s mid t(S value)Hfirst Hscan).
Qed.
End Skip.
Lemma machine230_skip_rows j:(j<8)%nat->
 Public230.tmn(machine230_skip_label(Datatypes.S j))false=Some(false,TM.R,machine230_skip_label j) /\
 Public230.tmn(machine230_skip_label j)true=Some(true,TM.R,machine230_skip_label j).
Proof.
 intro H. do 8(destruct j as[|j];[split;reflexivity|]). lia.
Qed.
Corollary machine230_skip_register M j value left tail word s:(j<8)%nat->
 machine230_unary_block M value tail word ->
 machine230_right_view M(machine230_skip_label(Datatypes.S j))left word s ->
 exists p k t,power2 M(succM M value)p /\p=succM M k /\
 machine230_right_view M(machine230_skip_label j)
 (addM M(mulM M p(mulM M(code_numeral M 2)left))k)tail t /\
 machine230_reaches_in M(succM M(succM M value))s t.
Proof.
 intros Hj Hb Hs. destruct(machine230_skip_rows j Hj)as[H0 H1].
 exact(machine230_skip_one_block M _ _ value left tail word s H0 H1 Hb Hs).
Qed.
Print Assumptions machine230_skip_one_block.
Print Assumptions machine230_skip_register.
