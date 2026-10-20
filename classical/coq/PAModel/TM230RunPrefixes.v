(** Compositional homogeneous words, with actual internally long TM scans. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 TM230LiteralActions TM230BinaryStep TM230Paths TM230BitArithmetic TM230ScanRight
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive PowerTwoLaws.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_run_prefix M b n tail word:=exists p k,
 power2 M n p /\p=succM M k /\
 word=addM M(mulM M k(machine230_bitM M b))(mulM M p tail).
Definition machine230_run_prefix_formula b n tail word:form:=∃∃
 (power2_formula(code_lift2 n)$1 ∧($1==σ $0 ∧
 code_lift2 word==($0⊗num(machine230_bit b)⊕$1⊗code_lift2 tail))).
Local Opaque holds power2_formula.
Lemma machine230_run_prefix_formula_correct M rho b n tail word:
 holds M rho(machine230_run_prefix_formula b n tail word)<->
 machine230_run_prefix M b(evalM M rho n)(evalM M rho tail)(evalM M rho word).
Proof.
 unfold machine230_run_prefix_formula,machine230_run_prefix.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite power2_formula_correct. setoid_rewrite machine230_holds_equal.
 repeat setoid_rewrite machine230_eval_add. repeat setoid_rewrite machine230_eval_mul.
 repeat setoid_rewrite code_eval_lift2. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Section Prefix.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation one := (S Z).
Local Notation two := (S one).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring machine230_prefix_ring : (model_semiring M).
Theorem machine230_run_prefix_total b n tail:exists word,machine230_run_prefix M b n tail word.
Proof.
 destruct(power2_total M n)as[p Hp]. destruct(power2_positive_successor M n p Hp)as[k Hk].
 exists(k*machine230_bitM M b+p*tail). exists p,k. auto.
Qed.
Theorem machine230_run_prefix_functional b n tail x y:
 machine230_run_prefix M b n tail x->machine230_run_prefix M b n tail y->x=y.
Proof.
 intros[p[k[Hp[Hpk Hx]]]][q[j[Hq[Hqj Hy]]]].
 assert(Ep:p=q)by(exact(power2_functional M n p q Hp Hq)).
 assert(Ek:k=j)by(apply(succ_injective M);congruence). congruence.
Qed.
Lemma machine230_run_prefix_zero b tail word:
 machine230_run_prefix M b Z tail word<->word=tail.
Proof.
 split.
 -intros[p[k[Hp[Hpk Hword]]]]. pose proof(power2_zero_value M p Hp)as Ep.
  assert(Ek:k=Z)by(apply(succ_injective M);now rewrite <-Hpk,Ep).
  subst p k. rewrite Hword,(succ_as_add M Z). ring.
 -intro E. subst word. exists one,Z. split;[apply power2_zero|]. split;[reflexivity|].
  rewrite(succ_as_add M Z). ring.
Qed.
Theorem machine230_run_prefix_successor b n tail word:
 machine230_run_prefix M b(S n)tail word <->
 exists inner,machine230_run_prefix M b n tail inner /\word=machine230_bitM M b+two*inner.
Proof.
 split.
 -intros[p[k[Hp[Hpk Hword]]]].
  destruct(power2_successor_inv M n p Hp)as[q[Hq Ep]]. change(p=two*q)in Ep.
  destruct(power2_positive_successor M n q Hq)as[j Hj].
  assert(Ek:k=S(two*j)).
  {apply(succ_injective M). rewrite <-Hpk,Ep,Hj.
   rewrite(succ_as_add M j),(succ_as_add M(S(two*j))),(succ_as_add M(two*j)),(succ_as_add M one). ring. }
  exists(j*machine230_bitM M b+q*tail). split;[exists q,j;auto|].
  rewrite Hword,Ep,Ek,Hj. rewrite(succ_as_add M j),(succ_as_add M(two*j)),(succ_as_add M one). ring.
 -intros[inner[[q[j[Hq[Hqj Hi]]]]Hw]].
  exists(two*q),(S(two*j)). split;[now apply power2_successor|]. split.
  +rewrite Hqj. rewrite(succ_as_add M j),(succ_as_add M(S(two*j))),(succ_as_add M(two*j)),(succ_as_add M one). ring.
  +rewrite Hw,Hi,Hqj. rewrite(succ_as_add M j),(succ_as_add M(two*j)),(succ_as_add M one). ring.
Qed.
Theorem machine230_run_prefix_add b n m tail inner word:
 machine230_run_prefix M b m tail inner->machine230_run_prefix M b n inner word->
 machine230_run_prefix M b(n+m)tail word.
Proof.
 intros[q[j[Hq[Hqj Hi]]]][p[k[Hp[Hpk Hw]]]].
 exists(p*q),(k+p*j). split;[exact(power2_add M n p Hp m q Hq)|]. split.
 -rewrite Hqj,Hpk. rewrite(succ_as_add M(k+S k*j)),(succ_as_add M j),(succ_as_add M k). ring.
 -rewrite Hw,Hi. ring.
Qed.
Theorem machine230_scan_prefix_right q b w n l tail word s:
 Public230.tmn q b=Some(w,TM.R,q)->
 machine230_run_prefix M b n tail word ->machine230_right_view M q l word s->
 exists final_l t,machine230_right_view M q final_l tail t /\machine230_reaches M s t.
Proof.
 intros Htable[p[k[Hp[Hpk Hword]]]]Hs.
 set(final_l:=p*l+k*machine230_bitM M w).
 destruct(machine230_right_view_total M q final_l tail)as[t Ht].
 exists final_l,t. split;[exact Ht|].
 destruct s as[sq sl sh sr],t as[tq tl th tr].
 unfold machine230_right_view in Hs,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs,Ht.
 destruct Hs as[Hsq[Hsl[Hsh Hsw]]],Ht as[Htq[Htl[Hth Htw]]].
 subst sq sl tq tl.
 apply(machine230_scan_right M q b w Htable n p k l sh sr th tr Hp Hpk Hsh Hth).
 change(sh+two*sr=k*machine230_bitM M b+p*(th+two*tr)).
 rewrite Hword in Hsw. rewrite Htw in Hsw. replace(sh+two*sr)with(two*sr+sh)by ring. rewrite <-Hsw. ring.
Qed.
End Prefix.
Print Assumptions machine230_run_prefix_formula_correct.
Print Assumptions machine230_run_prefix_add.
Print Assumptions machine230_scan_prefix_right.
