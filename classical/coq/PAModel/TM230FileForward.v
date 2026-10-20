(** Exact q64 movement through ordinary prefixes and into a marked target. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230Paths TM230ExactPaths TM230UnaryBlocks TM230ReverseBlocks
 TM230RegisterPrefix TM230FileEntryBlock PowerTwoSyntax.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_entry_encoding M(b:bool)value tail word:=
 if b then machine230_unary_block M value tail word else machine230_marked_block M value tail word.
Section Forward.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_forward_ring:(model_semiring M).
Theorem machine230_encoded_file_entry b value left tail word s:
 machine230_entry_encoding M b value tail word ->machine230_right_view M 64 left word s ->
 exists reverse t,machine230_reverse_block M value left reverse /\
 machine230_right_view M(machine230_file_scan_state b)reverse tail t /\machine230_reaches_in M(S(S value))s t.
Proof.
 intros Hb Hs.
 assert(Hdecomp:exists p k,power2 M value p /\p=S k /\
  word=two*machine230_bitM M b+four*(k+p*tail)).
 {destruct b.
  -destruct(machine230_marked_block_total M value tail)as[mark Hmark].
   pose proof(machine230_plain_marked_difference M value tail word mark Hb Hmark)as Hdiff.
   change(word=mark+two)in Hdiff. destruct Hmark as[p[k[Hp[Hpk Hmark]]]].
   change(mark=four*k+(four*p)*tail)in Hmark.
   exists p,k. split;[exact Hp|]. split;[exact Hpk|].
   change(word=two*one+four*(k+p*tail)). rewrite Hdiff,Hmark,(succ_as_add M Z);ring.
  -destruct Hb as[p[k[Hp[Hpk Hword]]]]. change(word=four*k+(four*p)*tail)in Hword.
   exists p,k. split;[exact Hp|]. split;[exact Hpk|]. change(word=two*Z+four*(k+p*tail)). rewrite Hword;ring. }
 destruct Hdecomp as[p[k[Hp[Hpk Hword]]]]. rewrite Hword in Hs.
 destruct(machine230_file_entry_block M b value p k left tail s Hp Hpk Hs)as[t[Ht Hpath]].
 exists(p*(four*left+one)+k),t. split.
 -exists p,k. split;[exact Hp|]. split;[exact Hpk|].
  change(p*(four*left+one)+k=one+two*(k+p*(two*left))).
  assert(F:four=two*two).
  {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
  rewrite Hpk,F,(succ_as_add M k),(succ_as_add M one);ring.
 -split;assumption.
Qed.
Theorem machine230_forward_prefix values left tail word reverse s:
 machine230_prefix_frame M values left tail word reverse ->machine230_right_view M 64 left word s ->
 exists t,machine230_right_view M 64 reverse tail t /\machine230_reaches M s t.
Proof.
 revert left word reverse s. induction values as[|v vs IH];intros left word reverse s Hframe Hs.
 -destruct Hframe as[-> ->]. exists s. split;[exact Hs|apply machine230_reaches_refl].
 -destruct Hframe as[middle[nextleft[Hb[Hrev Hframe]]]].
  destruct(machine230_encoded_file_entry true v left middle word s Hb Hs)as[out[mid[Hout[Hmid Hpath]]]].
  assert(E:out=nextleft)by(eapply machine230_reverse_block_functional;eassumption). subst out.
  destruct(IH nextleft middle reverse mid Hframe Hmid)as[t[Ht Htail]].
  exists t. split;[exact Ht|]. eapply machine230_reaches_trans;[|exact Htail].
  eapply machine230_reaches_in_forget;exact Hpath.
Qed.
End Forward.
Print Assumptions machine230_encoded_file_entry.
Print Assumptions machine230_forward_prefix.
