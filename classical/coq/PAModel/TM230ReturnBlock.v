(** Actual return motion across one ordinary unary file block. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230ExactPaths TM230ScanLeftExact TM230UnaryBlocks PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Return.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_return_ring:(model_semiring M).
Theorem machine230_return_one_block q qa qb value p k left right s:
 Public230.tmn q true=Some(true,TM.L,qa)->
 Public230.tmn qa true=Some(true,TM.L,qa)->
 Public230.tmn qa false=Some(false,TM.L,qb)->
 power2 M value p->p=S k->
 machine230_left_view M q right(one+two*(k+p*(two*left)))s ->
 exists word t,machine230_unary_block M value right word /\
 machine230_left_view M qb word left t /\machine230_reaches_in M(S(S value))s t.
Proof.
 intros HE HS HX Hp Hpk Hs.
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 set(rest:=k+p*(two*left)). set(scanright:=p*(two*right+one)+k).
 set(word:=two*scanright).
 destruct(machine230_left_view_total M qa(two*right+one)rest)as[mid Hmid].
 destruct(machine230_left_view_total M qa scanright(two*left))as[next Hnext].
 destruct(machine230_left_view_total M qb word left)as[t Ht].
 assert(Hfirst:machine230_step M s mid).
 {exact(machine230_left_view_step M q true true qa right rest s mid HE Hs Hmid). }
 assert(Hscan:machine230_reaches_in M value mid next).
 {destruct mid as[mq ml mh mr],next as[nq nl nh nr].
  unfold machine230_left_view in Hmid,Hnext;cbn[machine230_state machine230_left machine230_head machine230_right]in Hmid,Hnext.
  destruct Hmid as[Hmq[Hmr[Hmh Hmw]]],Hnext as[Hnq[Hnr[Hnh Hnw]]]. subst mq mr nq nr.
  unfold scanright. replace(p*(two*right+one)+k)with(p*(two*right+one)+k*machine230_bitM M true)
   by(change(p*(two*right+one)+k*one=p*(two*right+one)+k);rewrite(succ_as_add M Z);ring).
  apply(machine230_scan_left_exact M qa true true HS value p k(two*right+one)mh ml nh nl Hp Hpk Hmh Hnh).
  change(mh+two*ml=k*one+p*(nh+two*nl)).
  unfold rest in Hmw. rewrite Hnw in Hmw. replace(mh+two*ml)with(two*ml+mh)by ring.
  rewrite <-Hmw,(succ_as_add M Z). ring. }
 assert(Hlast:machine230_step M next t).
 {apply(machine230_left_view_step M qa false false qb scanright left next t HX).
  -change(machine230_left_view M qa scanright(Z+two*left)next).
   replace(Z+two*left)with(two*left)by ring. exact Hnext.
  -change(machine230_left_view M qb(two*scanright+Z)left t).
   replace(two*scanright+Z)with word;[exact Ht|unfold word;ring]. }
 exists word,t. split.
 -replace word with(four*(k+p*right)+two).
  +apply machine230_marked_block_plain. exists p,k. split;[exact Hp|]. split;[exact Hpk|]. ring.
  +unfold word,scanright. rewrite Hpk,F,(succ_as_add M k),(succ_as_add M one). ring.
 -split;[exact Ht|].
  pose proof(machine230_reaches_in_join M value one mid next t Hscan(machine230_reaches_in_one M next t Hlast))as Htail.
  replace(value+one)with(S value)in Htail.
  +exact(machine230_reaches_in_step M s mid t(S value)Hfirst Htail).
  +rewrite(Arithmetic.add_comm M value one),(Arithmetic.add_succ M Z value),(Arithmetic.add_zero M value). reflexivity.
Qed.
End Return.
Corollary machine230_return_file_block M value p k left right s:
 power2 M value p->p=succM M k->
 machine230_left_view M 40 right
 (addM M(succM M(zeroM M))(mulM M(code_numeral M 2)
 (addM M k(mulM M p(mulM M(code_numeral M 2)left)))))s ->
 exists word t,machine230_unary_block M value right word /\
 machine230_left_view M 40 word left t /\machine230_reaches_in M(succM M(succM M value))s t.
Proof. exact(machine230_return_one_block M 40 54 40 value p k left right s eq_refl eq_refl eq_refl). Qed.
Print Assumptions machine230_return_one_block.
Print Assumptions machine230_return_file_block.
