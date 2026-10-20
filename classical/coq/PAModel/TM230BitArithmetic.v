(** Binary stack decomposition and concrete one-step calibration in any PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing CodeExpressions
 TM230LiteralActions TM230TransitionArithmetic TM230BinaryStep TM230Paths.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_bitM M b:=code_numeral M(machine230_bit b).
Section Bits.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation one := (S Z).
Local Notation two := (S one).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring machine230_bits_ring : (model_semiring M).
Definition machine230_is_bit(x:D):Prop:=x=Z \/ x=one.
Lemma machine230_bit_is_bit b:machine230_is_bit(machine230_bitM M b).
Proof. destruct b;[right|left];reflexivity. Qed.
Lemma machine230_bit_lt x:machine230_is_bit x->coding_lt M x two.
Proof.
 intros[-> | ->];[eapply coding_lt_trans;apply coding_lt_succ|apply coding_lt_succ].
Qed.
Lemma machine230_pop_total x:
 exists h r,machine230_is_bit h /\ x=two*r+h.
Proof.
 destruct(remainder_total M x two(coding_zero_lt_succ M one))as[h[Hh[r E]]].
 exists h,r. split;[|rewrite E;ring].
 apply coding_lt_succ_cases in Hh. destruct Hh as[Hh|E1];[|now right].
 apply coding_lt_succ_cases in Hh. destruct Hh as[Hh|E0];[exfalso;exact(coding_not_lt_zero M h Hh)|now left].
Qed.
Lemma machine230_pop_unique h r h' r':
 machine230_is_bit h ->machine230_is_bit h' ->two*r+h=two*r'+h' ->h=h' /\ r=r'.
Proof.
 intros Hh Hh' E.
 assert(H1:remainder M(two*r+h)two h).
 { split;[now apply machine230_bit_lt|]. exists r. ring. }
 assert(H2:remainder M(two*r+h)two h').
 { split;[now apply machine230_bit_lt|]. exists r'. rewrite E;ring. }
 pose proof(remainder_unique M _ _ _ _ H1 H2)as H. split;[exact H|].
 apply(double_cancel M). unfold twoM. apply(Arithmetic.add_cancel M(two*r)(two*r')h).
 rewrite <-H in E. exact E.
Qed.
Definition machine230_right_view(q:nat)(left word:D)(s:machine230_config D):Prop:=
 machine230_state s=code_numeral M q /\ machine230_left s=left /\
 machine230_is_bit(machine230_head s) /\ word=two*machine230_right s+machine230_head s.
Lemma machine230_right_view_total q l word:
 exists s,machine230_right_view q l word s.
Proof.
 destruct(machine230_pop_total word)as[h[r[Hh E]]].
 exists(machine230_mk_config D(code_numeral M q)l h r). unfold machine230_right_view;cbn. auto.
Qed.
Lemma machine230_right_view_unique q l word s t:
 machine230_right_view q l word s ->machine230_right_view q l word t ->s=t.
Proof.
 destruct s as[sq sl sh sr],t as[tq tl th tr].
 unfold machine230_right_view;cbn. intros[Hq[Hl[Hh Hword]]][Kq[Kl[Kh Kword]]].
 destruct(machine230_pop_unique sh sr th tr Hh Kh (eq_trans(eq_sym Hword)Kword))as[Eh Er]. now subst.
Qed.
Lemma machine230_literal_transition q b w d q':
 Public230.tmn q b=Some(w,d,q')->
 machine230_transition M(code_numeral M q)(machine230_bitM M b)(machine230_bitM M w)
 (code_numeral M(machine230_direction d))(code_numeral M q').
Proof.
 intro H. exists(q,b,w,d,q'). split;[now apply machine230_action_exact|].
 unfold machine230_action_relation,machine230_bitM;cbn. auto.
Qed.
Theorem machine230_right_view_step q b w q' l tail s t:
 Public230.tmn q b=Some(w,TM.R,q')->
 machine230_right_view q l(machine230_bitM M b+two*tail)s ->
 machine230_right_view q'(two*l+machine230_bitM M w)tail t ->
 machine230_step M s t.
Proof.
 intros Htable Hs Ht. destruct s as[sq sl sh sr],t as[tq tl th tr].
 unfold machine230_right_view in Hs,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs,Ht.
 destruct Hs as[Hq[Hl[Hh Hword]]],Ht as[Kq[Kl[Kh Kword]]].
 destruct(machine230_pop_unique sh sr(machine230_bitM M b)tail Hh(machine230_bit_is_bit b)
 ltac:(eapply eq_trans;[exact(eq_sym Hword)|ring]))as[Eh Er]. subst sq sl sh sr tq tl.
 unfold machine230_step;cbn. exists(machine230_bitM M w),(code_numeral M(machine230_direction TM.R)).
 split;[now apply machine230_literal_transition|]. split;[exact Kh|].
 right. split;[reflexivity|]. split;[reflexivity|]. exact Kword.
Qed.
End Bits.
Print Assumptions machine230_pop_total.
Print Assumptions machine230_pop_unique.
Print Assumptions machine230_right_view_step.
