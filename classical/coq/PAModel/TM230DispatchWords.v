(** Compact arithmetic dispatcher words for the unchanged Runtime start/target
    syntax. Finite PC bits are composed directly, without large unary numerals. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BitArithmetic TM230RunPrefixes
 TM230SymbolicSegments TM230SymbolicCells TM230RuntimeWords TM230RuntimeTokens
 TM230RuntimeSites PowerTwoSyntax PowerTwoPositive.
From K230 Require Runtime230Core Interpreter230Sites.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint machine230_dispatch_bits M(bits:list bool)tail:=
 match bits with[]=>tail|b::bits=>addM M(machine230_bitM M b)
  (mulM M(succM M(succM M(zeroM M)))(machine230_dispatch_bits M bits tail))end.
Definition machine230_dispatch_conf bits constant box:Runtime230.sconf:=
 (84,false,[Runtime230.SB true],map Runtime230.SB bits++
  [Runtime230.SR false 1 constant;Runtime230.SB true;Runtime230.SBox box]).
Definition machine230_dispatch_view M bits gap constant word s:=exists p,
 power2 M(addM M gap(code_numeral M constant))p /\machine230_right_view M 84(succM M(zeroM M))
 (machine230_dispatch_bits M bits(mulM M p(addM M(succM M(zeroM M))
  (mulM M(succM M(succM M(zeroM M)))word))))s.
Section Words.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_dispatch_ring:(model_semiring M).
Theorem machine230_runtime_cells_word gap Box bits tail word:
 machine230_runtime_flat M gap Box(map Runtime230.SB bits++tail)word <->
 exists last,machine230_runtime_flat M gap Box tail last /\word=machine230_dispatch_bits M bits last.
Proof.
 revert word. induction bits as[|b bits IH];intro word.
 -cbn. split;[intro H;exists word;auto|intros[last[H ->]];exact H].
 -cbn[machine230_runtime_flat map app]. split.
  +intros[mid[Hmid Hcell]]. apply IH in Hmid. destruct Hmid as[last[Hlast Emid]].
   apply machine230_cell_value in Hcell. subst mid. exists last;split;[exact Hlast|exact Hcell].
  +intros[last[Hlast ->]]. exists(machine230_dispatch_bits M bits last);split.
   *apply IH;exists last;auto.
   *apply machine230_cell_value;reflexivity.
Qed.
Lemma machine230_zero_prefix_power n tail word:
 machine230_run_prefix M false n tail word <->exists p,power2 M n p /\word=p*tail.
Proof.
 split.
 -intros[p[k[Hp[Hpk Hw]]]]. exists p;split;[exact Hp|]. change(word=k*Z+p*tail)in Hw.
  rewrite Hw;ring.
 -intros[p[Hp ->]]. destruct(power2_positive_successor M n p Hp)as[k Hpk].
  exists p,k;split;[exact Hp|]. split;[exact Hpk|]. change(p*tail=k*Z+p*tail);ring.
Qed.
Lemma machine230_runtime_header gap Box box header:
 machine230_runtime_flat M gap Box[Runtime230.SB true;Runtime230.SBox box]header <->
 exists word,Box box word /\header=one+two*word.
Proof.
 cbn[machine230_runtime_flat]. setoid_rewrite machine230_cell_value.
 split;[intros[word[[_ HB]H]];exists word;auto|intros[word[HB H]];exists word;split;[split;[reflexivity|exact HB]|exact H]].
Qed.
Theorem machine230_runtime_dispatch_words gap Box bits constant box s:
 machine230_runtime_view M gap Box(machine230_dispatch_conf bits constant box)s <->
 exists word,Box box word /\machine230_dispatch_view M bits gap constant word s.
Proof.
 unfold machine230_dispatch_conf,machine230_runtime_view,machine230_dispatch_view.
 split.
 -intros[l[r[[blank[Hblank Hleft]][Hright Hs]]]].
  change(blank=Z)in Hblank;subst blank. apply machine230_cell_value in Hleft.
  change(l=one+two*Z)in Hleft. assert(El:l=one)by(rewrite Hleft;ring). rewrite El in Hs.
  apply machine230_runtime_cells_word in Hright. destruct Hright as[padding[Hpadding Er]].
  destruct Hpadding as[header[Hheader Hrun]].
  apply machine230_runtime_header in Hheader. destruct Hheader as[word[HB Eheader]].
  unfold machine230_segment_value,machine230_segment_length in Hrun.
  change(machine230_run_prefix M false(one*gap+N constant)header padding)in Hrun.
  rewrite Arithmetic.mul_one in Hrun. apply machine230_zero_prefix_power in Hrun.
  destruct Hrun as[p[Hp Epadding]].
  exists word;split;[exact HB|]. exists p;split;[exact Hp|].
  rewrite Er,Epadding,Eheader in Hs;exact Hs.
 -intros[word[HB[p[Hp Hs]]]].
  exists one,(machine230_dispatch_bits M bits(p*(one+two*word)));split.
  +exists Z;split;[reflexivity|]. apply machine230_cell_value;change(one=one+two*Z);ring.
  +split;[|exact Hs]. apply machine230_runtime_cells_word.
   exists(p*(one+two*word));split;[|reflexivity].
   exists(one+two*word);split.
   *apply machine230_runtime_header;exists word;auto.
   *unfold machine230_segment_value,machine230_segment_length.
    change(machine230_run_prefix M false(one*gap+N constant)(one+two*word)(p*(one+two*word))).
    rewrite Arithmetic.mul_one. apply machine230_zero_prefix_power;exists p;auto.
Qed.
Corollary machine230_runtime_start_words gap Box bits s:
 machine230_runtime_view M gap Box(Sites230.start bits)s <->
 exists word,Box(Runtime230.BPlain Runtime230.FNone)word /\
 machine230_dispatch_view M bits gap(Sites230.D0-length bits)word s.
Proof. exact(machine230_runtime_dispatch_words gap Box bits(Sites230.D0-length bits)(Runtime230.BPlain Runtime230.FNone)s). Qed.
Corollary machine230_runtime_target_words gap Box bits overflow box s:
 machine230_runtime_view M gap Box(Sites230.tgt_conf bits overflow box)s <->
 exists word,Box box word /\machine230_dispatch_view M bits gap
  (Sites230.D0+(if overflow then 1 else 0)+Sites230.growth box-length bits)word s.
Proof.
 exact(machine230_runtime_dispatch_words gap Box bits
  (Sites230.D0+(if overflow then 1 else 0)+Sites230.growth box-length bits)box s).
Qed.
Theorem machine230_dispatch_rebase bits gap base extra used word s:
 (used<=base)%nat->
 (machine230_dispatch_view M bits gap(base+extra-used)word s <->
 machine230_dispatch_view M bits(gap+N extra)(base-used)word s).
Proof.
 intro Hbound. assert(EN:(base+extra-used=extra+(base-used))%nat)by lia.
 unfold machine230_dispatch_view. rewrite EN,machine230_runtime_numeral_add.
 replace(gap+(N extra+N(base-used)))with((gap+N extra)+N(base-used))by ring;reflexivity.
Qed.
End Words.
Print Assumptions machine230_runtime_cells_word.
Print Assumptions machine230_runtime_dispatch_words.
Print Assumptions machine230_runtime_start_words.
Print Assumptions machine230_runtime_target_words.
Print Assumptions machine230_dispatch_rebase.

