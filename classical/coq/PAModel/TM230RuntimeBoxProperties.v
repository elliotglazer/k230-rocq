(** Determinacy and delimiter facts for the concrete runtime box word. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions TM230UnaryBlocks TM230RegisterPrefix
 TM230SpareSyntax TM230SpareRecurrence TM230RuntimeBox.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Properties.
Variable M:Model.
Local Notation Z:=(zeroM M).
Lemma machine230_predecessor_unique old x y:
 ((old=Z /\x=Z)\/old=succM M x)->((old=Z /\y=Z)\/old=succM M y)->x=y.
Proof.
 intros[[Hox Hx]|Hx][[Hoy Hy]|Hy].
 -congruence.
 -exfalso;exact(zero_ne_succ M y ltac:(congruence)).
 -exfalso;exact(zero_ne_succ M x ltac:(congruence)).
 -apply(succ_injective M);congruence.
Qed.
Lemma machine230_effect_values_unique eff values a b:
 machine230_effect_values M eff values a->machine230_effect_values M eff values b->a=b.
Proof.
 destruct eff;cbn[machine230_effect_values];intros HA HB.
 -congruence.
 -destruct HA as[old[HA ->]],HB as[old'[HB ->]].
  assert(old=old')by congruence. now subst old'.
 -destruct HA as[old[x[HA[HX ->]]]],HB as[old'[y[HB[HY ->]]]].
  assert(old=old')by congruence. subst old'.
  now rewrite(machine230_predecessor_unique old x y HX HY).
Qed.
Lemma machine230_blocks_list_unique values tail a b:
 machine230_blocks_list M values tail a->machine230_blocks_list M values tail b->a=b.
Proof.
 induction values as[|v values IH]in a,b|-*;cbn[machine230_blocks_list].
 -congruence.
 -intros[inside[HI HA]][inside'[HI' HB]].
  pose proof(IH inside inside' HI HI')as E. subst inside'.
  exact(machine230_unary_block_functional M v inside a b HA HB).
Qed.
Lemma machine230_marked_blocks_list_unique values r tail a b:
 machine230_marked_blocks_list M r values tail a->machine230_marked_blocks_list M r values tail b->a=b.
Proof.
 induction values as[|v values IH]in r,a,b|-*;destruct r;cbn;try contradiction.
 -intros[inside[HI HA]][inside'[HI' HB]].
  pose proof(machine230_blocks_list_unique values tail inside inside' HI HI')as E. subst inside'.
  exact(machine230_marked_block_functional M v inside a b HA HB).
 -intros[inside[HI HA]][inside'[HI' HB]].
  pose proof(IH r inside inside' HI HI')as E. subst inside'.
  exact(machine230_unary_block_functional M v inside a b HA HB).
Qed.
Theorem machine230_runtime_box_unique values E x a b:
 machine230_runtime_box M values E x a->machine230_runtime_box M values E x b->a=b.
Proof.
 destruct x as[eff|r];intros[HL[HE HA]][_[_ HB]];cbn in HA,HB.
 -destruct HA as[va[sa[HVA[HSA HA]]]],HB as[vb[sb[HVB[HSB HB]]]].
  assert(Ev:va=vb)by(eapply machine230_effect_values_unique;eassumption). subst vb.
  assert(Es:sa=sb)by(eapply machine230_spare_functional;eassumption). subst sb.
  exact(machine230_blocks_list_unique va sa a b HA HB).
 -destruct HA as[sa[HSA HA]],HB as[sb[HSB HB]].
  assert(Es:sa=sb)by(eapply machine230_spare_functional;eassumption). subst sb.
  exact(machine230_marked_blocks_list_unique values r sa a b HA HB).
Qed.
Lemma machine230_blocks_list_head values tail word:
 values<>[]->machine230_blocks_list M values tail word->
 exists rest,word=mulM M(code_numeral M 2)rest.
Proof.
 destruct values as[|v values];[contradiction|]. intros _[inside[HI HB]].
 exact(machine230_unary_block_even M v inside word HB).
Qed.
Lemma machine230_marked_blocks_list_head values r tail word:
 machine230_marked_blocks_list M r values tail word->
 exists rest,word=mulM M(code_numeral M 2)rest.
Proof.
 destruct values as[|v values];destruct r;cbn;try contradiction;intros[inside[HI HB]].
 -exact(machine230_marked_block_even M v inside word HB).
 -exact(machine230_unary_block_even M v inside word HB).
Qed.
Theorem machine230_runtime_box_head values E x word:
 machine230_runtime_box M values E x word->exists rest,word=mulM M(code_numeral M 2)rest.
Proof.
 destruct x as[eff|r];intros[HL[HE HB]];cbn in HB.
 -destruct HB as[updated[spare[HU[HS HW]]]].
  apply(machine230_blocks_list_head updated spare word);[|exact HW].
  intro EN. pose proof(machine230_effect_length M eff values updated HU)as Hlength.
  rewrite EN in Hlength. cbn in Hlength. lia.
 -destruct HB as[spare[HS HW]]. exact(machine230_marked_blocks_list_head values r spare word HW).
Qed.
Lemma machine230_blocks_list_total values tail:exists word,machine230_blocks_list M values tail word.
Proof.
 induction values as[|v values IH];[exists tail;reflexivity|].
 destruct IH as[inside HI]. destruct(machine230_unary_block_total M v inside)as[word HW].
 exists word,inside;auto.
Qed.
Theorem machine230_runtime_plain_total values E:
 length values=9%nat->coding_lt M Z E->exists word,
 machine230_runtime_box M values E(Runtime230.BPlain Runtime230.FNone)word.
Proof.
 intros HL HE. destruct(machine230_spare_total M E)as[spare HS].
 destruct(machine230_blocks_list_total values spare)as[word HW].
 exists word. split;[exact HL|]. split;[exact HE|]. exists values,spare.
 split;[reflexivity|]. auto.
Qed.
End Properties.
Print Assumptions machine230_runtime_box_unique.
Print Assumptions machine230_runtime_box_head.
Print Assumptions machine230_runtime_plain_total.