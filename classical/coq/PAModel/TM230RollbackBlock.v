(** One complete rollback block for the prefix-carry runtime. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230ExactPaths TM230ScanLeftExact TM230UnaryBlocks PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Rollback.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_rollback_ring:(model_semiring M).
Theorem machine230_rollback_one_block value p k left right s:
 power2 M value p->p=S k->
 machine230_left_view M 97 right(p*(four*left+two)+k)s ->
 exists word t,machine230_unary_block M value right word /\
 machine230_left_view M 97 word left t /\machine230_reaches_in M(S(S value))s t.
Proof.
 intros Hp Hpk Hs.
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 set(midright:=p*right+k). set(word:=two+four*(k+p*right)).
 destruct(machine230_left_view_total M 97 midright(four*left+two))as[mid Hmid].
 destruct(machine230_left_view_total M 113(two*midright+one)(one+two*left))as[next Hnext].
 destruct(machine230_left_view_total M 97 word left)as[t Ht].
 assert(Hscan:machine230_reaches_in M value s mid).
 {destruct s as[sq sl sh sr],mid as[mq ml mh mr].
  unfold machine230_left_view in Hs,Hmid;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs,Hmid.
  destruct Hs as[Hsq[Hsr[Hsh Hsw]]],Hmid as[Hmq[Hmr[Hmh Hmw]]]. subst sq sr mq mr.
  unfold midright. replace(p*right+k)with(p*right+k*machine230_bitM M true)by(change(p*right+k*one=p*right+k);rewrite(succ_as_add M Z);ring).
  apply(machine230_scan_left_exact M 97 true true eq_refl value p k right sh sl mh ml Hp Hpk Hsh Hmh).
  change(sh+two*sl=k*one+p*(mh+two*ml)).
  rewrite Hmw in Hsw. replace(sh+two*sl)with(two*sl+sh)by ring. rewrite <-Hsw,(succ_as_add M Z). ring. }
 assert(H1:machine230_step M mid next).
 {apply(machine230_left_view_step M 97 false true 113 midright(one+two*left)).
  -reflexivity.
  -change(machine230_left_view M 97 midright(Z+two*(one+two*left))mid).
   replace(Z+two*(one+two*left))with(four*left+two);[exact Hmid|]. rewrite F,(succ_as_add M one);ring.
  -exact Hnext. }
 assert(H2:machine230_step M next t).
 {apply(machine230_left_view_step M 113 true false 97(two*midright+one)left).
  -reflexivity.
  -exact Hnext.
  -change(machine230_left_view M 97(two*(two*midright+one)+Z)left t).
   replace(two*(two*midright+one)+Z)with word;[exact Ht|]. unfold word,midright;rewrite F,(succ_as_add M one);ring. }
 exists word,t. split.
 -replace word with(four*(k+p*right)+two)by(unfold word;ring).
  apply machine230_marked_block_plain. exists p,k. split;[exact Hp|]. split;[exact Hpk|]. ring.
 -split;[exact Ht|].
  pose proof(machine230_reaches_in_join M value(S one)s mid t Hscan
   (machine230_reaches_in_step M mid next t one H1(machine230_reaches_in_one M next t H2)))as Hpath.
  replace(value+S one)with(S(S value))in Hpath;[exact Hpath|].
  rewrite(Arithmetic.add_comm M value(S one)),(Arithmetic.add_succ M one value),
   (Arithmetic.add_succ M Z value),(Arithmetic.add_zero M value). reflexivity.
Qed.
End Rollback.
Print Assumptions machine230_rollback_one_block.
