(** One fixed value table and actual internal word histories for spare registers. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
 CodeExpressions NumericalProofs PowerTwoSyntax PowerTwoRecurrence
 TM230UnaryBlocks TM230RegisterWords TM230CarryChainSyntax TM230ChainRetailing
 TM230SpareSyntax TM230SpareRecurrence TM230SparePower TM230SpareBlocks.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_spare_chain_value_at M wb wc count tail distance :=forall i word spare p,
 count=addM M i distance ->beta M wb wc i word ->machine230_spare M distance spare ->
 power2 M(mulM M(code_numeral M 3)distance)p ->word=addM M spare(mulM M p tail).
Definition machine230_spare_chain_value_formula:form:=∀∀∀∀($5==$3⊕$4→beta_formula $6 $7 $3 $2→machine230_spare_formula $4 $1→power2_formula(num 3⊗$4)$0→$2==$1⊕$0⊗$8).
Local Opaque holds beta_formula machine230_spare_formula power2_formula.
Lemma machine230_spare_chain_value_definable M wb wc count tail:
 Definable1 M(machine230_spare_chain_value_at M wb wc count tail).
Proof.
 exists machine230_spare_chain_value_formula,(count.:wb.:wc.:tail.:(fun _=>zeroM M)). intro distance.
 unfold machine230_spare_chain_value_formula,machine230_spare_chain_value_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite beta_formula_correct. setoid_rewrite machine230_spare_formula_correct.
 setoid_rewrite power2_formula_correct. setoid_rewrite spare_holds_equal.
 repeat setoid_rewrite register_eval_add. repeat setoid_rewrite register_eval_mul.
 repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Section Chains.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Notation one:=(S Z).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring spare_chain_ring:(model_semiring M).
Ltac spare_chain_constants:=cbn[code_numeral];repeat multimatch goal with
 | |- context[succM M ?x]=>lazymatch x with
   | zeroM _=>fail 0
   | _=>rewrite(succ_as_add M x)
   end
 end.
Theorem machine230_spare_values_total count:
 exists vb vc,forall i,coding_lt M i count->beta M vb vc i one.
Proof.
 destruct(beta_pack_formula M(fun _=>Z)($0==num 1)count one)as[vb[vc HV]].
 -intros i Hi;exists one;reflexivity.
 -intros i r Hi Hr. change(r=one)in Hr. subst r. apply coding_lt_succ.
 -exists vb,vc. intros i Hi. destruct(HV i Hi)as[r[Hr HB]].
  change(r=one)in Hr. now subst r.
Qed.
Theorem machine230_spare_chain_value_uniform vb vc wb wc count tail:
 (forall i,coding_lt M i count->beta M vb vc i one)->
 machine230_carry_chain M vb vc wb wc count->beta M wb wc count tail->
 forall distance,machine230_spare_chain_value_at M wb wc count tail distance.
Proof.
 intros HV HC HT. apply(definable_induction M(machine230_spare_chain_value_at M wb wc count tail)
  (machine230_spare_chain_value_definable M wb wc count tail)).
 -intros i word spare p E HW HS HP.
  replace(i+Z)with i in E by ring. subst i.
  assert(Eword:word=tail)by(eapply beta_unique;eassumption).
  rewrite Eword,(machine230_spare_zero_value M spare HS).
  replace(N 3*Z)with Z in HP by ring. rewrite(power2_zero_value M p HP).
  spare_chain_constants;ring.
 -intros d IH i word spare p E HW HS HP.
  assert(Hi:coding_lt M i count).
  {exists d. rewrite(Arithmetic.add_comm M i(S d)),(Arithmetic.add_succ M d i),
    (Arithmetic.add_comm M d i)in E. exact E. }
  destruct(HC i Hi)as[v[w[next[Hv[Hw[Hnext HB]]]]]].
  assert(Ev:v=one)by(eapply beta_unique;[exact Hv|exact(HV i Hi)]).
  assert(Ew:w=word)by(eapply beta_unique;eassumption). subst v w.
  apply(proj1(machine230_unary_block_one M next word))in HB.
  destruct(machine230_spare_successor_inv M d spare HS)as[old[Hold Eold]].
  destruct(power2_total M(N 3*d))as[q Hq].
  assert(Ep:p=N 8*q)by(eapply power2_functional;[exact HP|now apply spare_power_step]).
  assert(Enext:next=old+q*tail).
  {apply(IH(S i)next old q);[|exact Hnext|exact Hold|exact Hq].
   rewrite(Arithmetic.add_succ M i d).
   rewrite(Arithmetic.add_comm M i(S d)),(Arithmetic.add_succ M d i),
    (Arithmetic.add_comm M d i)in E. exact E. }
  rewrite HB,Enext,Eold,Ep. ring.
Qed.
Theorem machine230_spare_chain_first vb vc wb wc count tail first word p:
 (forall i,coding_lt M i count->beta M vb vc i one)->
 machine230_carry_chain M vb vc wb wc count->beta M wb wc count tail->
 beta M wb wc Z first->machine230_spare M count word->power2 M(N 3*count)p->
 first=word+p*tail.
Proof.
 intros HV HC HT HF HW HP.
 apply(machine230_spare_chain_value_uniform vb vc wb wc count tail HV HC HT count Z first word p);
 [ring|exact HF|exact HW|exact HP].
Qed.
Theorem machine230_spare_chain_for_tail vb vc count word p tail:
 (forall i,coding_lt M i count->beta M vb vc i one)->
 machine230_spare M count word->power2 M(N 3*count)p->
 exists wb wc,machine230_carry_chain M vb vc wb wc count /\
 beta M wb wc Z(word+p*tail) /\beta M wb wc count tail.
Proof.
 intros HV HW HP. destruct(machine230_carry_chain_retail_total M vb vc count tail)
 as[wb[wc[first[HC[HF HT]]]]].
 pose proof(machine230_spare_chain_first vb vc wb wc count tail first word p HV HC HT HF HW HP)as E.
 exists wb,wc. rewrite <-E. auto.
Qed.
Theorem machine230_spare_chain_tables count:
 exists vb vc,(forall i,coding_lt M i count->beta M vb vc i one) /\
 forall word p,machine230_spare M count word->power2 M(N 3*count)p->
 forall tail,exists wb wc,machine230_carry_chain M vb vc wb wc count /\
 beta M wb wc Z(word+p*tail) /\beta M wb wc count tail.
Proof.
 destruct(machine230_spare_values_total count)as[vb[vc HV]]. exists vb,vc. split;[exact HV|].
 intros word p HW HP tail. exact(machine230_spare_chain_for_tail vb vc count word p tail HV HW HP).
Qed.
Theorem machine230_spare_zero_six_tables count word p:
 machine230_spare M count word->power2 M(N 3*count)p->
 exists vb vc wb wc db dc,
 (forall i,coding_lt M i count->beta M vb vc i one) /\
 machine230_carry_chain M vb vc wb wc count /\
 beta M wb wc Z word /\beta M wb wc count Z /\
 machine230_carry_chain M vb vc db dc count /\
 beta M db dc Z(word+N 6*p) /\beta M db dc count(N 6) /\
 machine230_spare M(S count)(word+N 6*p).
Proof.
 intros HW HP. destruct(machine230_spare_chain_tables count)as[vb[vc[HV Htables]]].
 destruct(Htables word p HW HP Z)as[wb[wc[HC[HF HT]]]].
 destruct(Htables word p HW HP(N 6))as[db[dc[HD[HG HU]]]].
 replace(word+p*Z)with word in HF by ring.
 replace(word+p*N 6)with(word+N 6*p)in HG by ring.
 exists vb,vc,wb,wc,db,dc. split;[exact HV|]. split;[exact HC|]. split;[exact HF|]. split;[exact HT|]. split;[exact HD|]. split;[exact HG|]. split;[exact HU|].
 exact(machine230_spare_append M count word p HW HP).
Qed.
End Chains.
Print Assumptions machine230_spare_values_total.
Print Assumptions machine230_spare_chain_value_uniform.
Print Assumptions machine230_spare_chain_tables.
Print Assumptions machine230_spare_zero_six_tables.