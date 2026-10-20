(** Arithmetic interpretation of the literal public symbolic runtime syntax.
    Box is a word graph; concrete register-file interpretation is supplied by
    the separate physical-file layer, not assumed correct here. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BinaryStep TM230BitArithmetic
 TM230LeftView TM230RunPrefixes TM230SymbolicSegments TM230SymbolicCells.
From K230 Require Runtime230Core.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Module Runtime230:=K230.Runtime230Core.
Fixpoint machine230_runtime_flat M gap(Box:Runtime230.boxst->carrier M->Prop)
 (ss:list Runtime230.seg)(word:carrier M):Prop:=
 match ss with
 |[]=>word=zeroM M
 |Runtime230.SB b::ss=>exists middle,machine230_runtime_flat M gap Box ss middle /\
   machine230_segment_value M gap(machine230_cell b)middle word
 |Runtime230.SR b a c::ss=>exists middle,machine230_runtime_flat M gap Box ss middle /\
   machine230_segment_value M gap(machine230_make_segment b a c)middle word
 |Runtime230.SBox x::ss=>ss=[] /\Box x word
 end.
Definition machine230_runtime_view M gap Box(conf:Runtime230.sconf)s:=
 let '(q,onleft,ls,rs):=conf in exists l r,
 machine230_runtime_flat M gap Box ls l /\machine230_runtime_flat M gap Box rs r /\
 if onleft then machine230_left_view M q r l s else machine230_right_view M q l r s.
Theorem machine230_runtime_flat_unique M gap Box:
 (forall x a b,Box x a->Box x b->a=b)->
 forall ss a b,machine230_runtime_flat M gap Box ss a->machine230_runtime_flat M gap Box ss b->a=b.
Proof.
 intros HBox ss. induction ss as[|[bit|bit factor constant|box]ss IH];intros a b Ha Hb.
 -change(a=zeroM M)in Ha;change(b=zeroM M)in Hb;congruence.
 -destruct Ha as[x[Hx Ha]],Hb as[y[Hy Hb]]. assert(E:x=y)by(eapply IH;eassumption). subst y.
  eapply machine230_run_prefix_functional;eassumption.
 -destruct Ha as[x[Hx Ha]],Hb as[y[Hy Hb]]. assert(E:x=y)by(eapply IH;eassumption). subst y.
  eapply machine230_run_prefix_functional;eassumption.
 -destruct Ha as[_ Ha],Hb as[_ Hb]. exact(HBox box a b Ha Hb).
Qed.
Theorem machine230_runtime_view_unique M gap Box conf s t:
 (forall x a b,Box x a->Box x b->a=b)->
 machine230_runtime_view M gap Box conf s->machine230_runtime_view M gap Box conf t->s=t.
Proof.
 intros HBox. destruct conf as[[[q onleft]ls]rs].
 intros[l[r[Hl[Hr Hs]]]][l'[r'[Hl'[Hr' Ht]]]].
 assert(El:l=l')by(eapply machine230_runtime_flat_unique;eassumption). subst l'.
 assert(Er:r=r')by(eapply machine230_runtime_flat_unique;eassumption). subst r'.
 destruct onleft;[eapply machine230_left_view_unique|eapply machine230_right_view_unique];eassumption.
Qed.
Theorem machine230_runtime_peel M gap Box b a c ss word:
 machine230_runtime_flat M gap Box(Runtime230.SR b a(Datatypes.S c)::ss)word <->
 machine230_runtime_flat M gap Box(Runtime230.SB b::Runtime230.SR b a c::ss)word.
Proof.
 cbn[machine230_runtime_flat]. setoid_rewrite (machine230_segment_peel M gap b a c).
 split.
 -intros[x[Hx[y[Hy Hcell]]]]. exists y;split;[exists x;auto|exact Hcell].
 -intros[y[[x[Hx Hy]]Hcell]]. exists x;split;[exact Hx|exists y;auto].
Qed.
Theorem machine230_runtime_empty_run M gap Box b ss word:
 machine230_runtime_flat M gap Box(Runtime230.SR b 0 0::ss)word <->
 machine230_runtime_flat M gap Box ss word.
Proof.
 cbn[machine230_runtime_flat]. unfold machine230_segment_value,machine230_segment_length.
 cbn[machine230_segment_factor machine230_segment_constant code_numeral].
 replace(addM M(mulM M(zeroM M)gap)(zeroM M))with(zeroM M)
  by(now rewrite Arithmetic.mul_zero,Arithmetic.add_zero).
 setoid_rewrite machine230_run_prefix_zero. split;[intros[x[Hx ->]];exact Hx|intro H;exists word;auto].
Qed.
Section Reorient.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation two:=(succM M(succM M Z)).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_runtime_ring:(model_semiring M).
Theorem machine230_views_reorient q b left right s:
 machine230_left_view M q right(machine230_bitM M b+two*left)s <->
 machine230_right_view M q left(machine230_bitM M b+two*right)s.
Proof.
 destruct s as[sq sl sh sr]. unfold machine230_left_view,machine230_right_view;
 cbn[machine230_state machine230_left machine230_head machine230_right]. split.
 -intros[Hq[Hr[Hbit Hword]]].
  destruct(machine230_pop_unique M sh sl(machine230_bitM M b)left Hbit(machine230_bit_is_bit M b)
   ltac:(rewrite <-Hword;ring))as[Eh El]. subst sq sr sh sl.
  split;[reflexivity|]. split;[reflexivity|]. split;[apply machine230_bit_is_bit|ring].
 -intros[Hq[Hl[Hbit Hword]]].
  destruct(machine230_pop_unique M sh sr(machine230_bitM M b)right Hbit(machine230_bit_is_bit M b)
   ltac:(rewrite <-Hword;ring))as[Eh Er]. subst sq sl sh sr.
  split;[reflexivity|]. split;[reflexivity|]. split;[apply machine230_bit_is_bit|ring].
Qed.
End Reorient.
Print Assumptions machine230_runtime_view_unique.
Print Assumptions machine230_runtime_peel.
Print Assumptions machine230_runtime_empty_run.
Print Assumptions machine230_views_reorient.



