(** The exact left-oriented binary tape view and one actual table step. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 TM230LiteralActions TM230TransitionArithmetic TM230BinaryStep TM230Paths TM230BitArithmetic.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section LeftView.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation two:=(succM M(succM M(zeroM M))).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_left_view_ring:(model_semiring M).
Definition machine230_left_view(q:nat)(right word:D)(s:machine230_config D):Prop:=
 machine230_state s=code_numeral M q /\machine230_right s=right /\
 machine230_is_bit M(machine230_head s) /\word=two*machine230_left s+machine230_head s.
Lemma machine230_left_view_total q r word:exists s,machine230_left_view q r word s.
Proof.
 destruct(machine230_pop_total M word)as[h[l[Hh E]]].
 exists(machine230_mk_config D(code_numeral M q)l h r).
 unfold machine230_left_view;cbn. auto.
Qed.
Lemma machine230_left_view_unique q r word s t:
 machine230_left_view q r word s->machine230_left_view q r word t->s=t.
Proof.
 destruct s as[sq sl sh sr],t as[tq tl th tr].
 unfold machine230_left_view;cbn. intros[Hq[Hr[Hh Hw]]][Kq[Kr[Kh Kw]]].
 destruct(machine230_pop_unique M sh sl th tl Hh Kh(eq_trans(eq_sym Hw)Kw))as[Eh El]. now subst.
Qed.
Theorem machine230_left_view_step q b w q' r tail s t:
 Public230.tmn q b=Some(w,TM.L,q')->
 machine230_left_view q r(machine230_bitM M b+two*tail)s->
 machine230_left_view q'(two*r+machine230_bitM M w)tail t->machine230_step M s t.
Proof.
 intros Htable Hs Ht. destruct s as[sq sl sh sr],t as[tq tl th tr].
 unfold machine230_left_view in Hs,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs,Ht.
 destruct Hs as[Hq[Hr[Hh Hw]]],Ht as[Kq[Kr[Kh Kw]]].
 destruct(machine230_pop_unique M sh sl(machine230_bitM M b)tail Hh(machine230_bit_is_bit M b)
  ltac:(eapply eq_trans;[exact(eq_sym Hw)|ring]))as[Eh El].
 subst sq sr sh sl tq tr. unfold machine230_step;cbn.
 exists(machine230_bitM M w),(code_numeral M(machine230_direction TM.L)).
 split;[now apply machine230_literal_transition|]. split;[exact Kh|].
 left. split;[reflexivity|]. split;[reflexivity|exact Kw].
Qed.
End LeftView.
Print Assumptions machine230_left_view_step.
