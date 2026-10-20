(** Arithmetic read of a length-sensitive PC code, with RM's implicit zero
    bits after the list ends. The sentinel is never consumed as a path bit. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 NumericalProofs TM230LiteralActions TM230BitArithmetic Program230PathCode.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Bool.Bool setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_path_pop M code head rest:Prop:=
 (code=succM M(zeroM M) /\head=zeroM M /\rest=succM M(zeroM M))\/
 (machine230_is_bit M head /\exists k,rest=succM M k /\
   code=addM M head(mulM M(code_numeral M 2)rest)).
Definition program230_path_pop_formula(code head rest:term):form:=
 ((code==num 1) ∧((head==zero) ∧(rest==num 1))) ∨
 ∃(((head`[↑]==zero) ∨(head`[↑]==num 1)) ∧
   ((rest`[↑]==σ $0) ∧(code`[↑]==head`[↑]⊕num 2⊗rest`[↑]))).
Lemma pathpop_holds_equal M rho t u:holds M rho(t==u)<->evalM M rho t=evalM M rho u.
Proof. reflexivity. Qed.
Lemma pathpop_eval_up M rho x t:evalM M(x.:rho)t`[↑]=evalM M rho t.
Proof. unfold evalM;now rewrite eval_up. Qed.
Lemma pathpop_eval_succ M rho t:evalM M rho(σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.
Lemma pathpop_eval_add M rho t u:evalM M rho(t⊕u)=addM M(evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Lemma pathpop_eval_mul M rho t u:evalM M rho(t⊗u)=mulM M(evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Theorem program230_path_pop_formula_correct M rho code head rest:
 holds M rho(program230_path_pop_formula code head rest)<->
 program230_path_pop M(evalM M rho code)(evalM M rho head)(evalM M rho rest).
Proof.
 unfold program230_path_pop_formula,program230_path_pop,machine230_is_bit.
 rewrite holds_or.
 assert(Htail:holds M rho(∃(((head`[↑]==zero) ∨(head`[↑]==num 1)) ∧
   ((rest`[↑]==σ $0) ∧(code`[↑]==head`[↑]⊕num 2⊗rest`[↑]))))<->
  ((evalM M rho head=zeroM M \/evalM M rho head=succM M(zeroM M)) /\
   exists k,evalM M rho rest=succM M k /\
    evalM M rho code=addM M(evalM M rho head)(mulM M(code_numeral M 2)(evalM M rho rest)))).
 {rewrite holds_ex. split.
  -intros[k H]. rewrite(holds_and M(k.:rho)((head`[↑]==zero) ∨(head`[↑]==num 1))
     ((rest`[↑]==σ $0) ∧(code`[↑]==head`[↑]⊕num 2⊗rest`[↑])))in H.
   destruct H as[Hb Hr]. rewrite holds_or,!pathpop_holds_equal,!pathpop_eval_up,code_eval_num in Hb.
   rewrite holds_and,!pathpop_holds_equal,pathpop_eval_add,pathpop_eval_mul,
     !pathpop_eval_up,pathpop_eval_succ,code_eval_num in Hr.
   split;[exact Hb|exists k;exact Hr].
  -intros[Hb[k Hr]];exists k.
   rewrite(holds_and M(k.:rho)((head`[↑]==zero) ∨(head`[↑]==num 1))
     ((rest`[↑]==σ $0) ∧(code`[↑]==head`[↑]⊕num 2⊗rest`[↑]))).
   split.
   +rewrite holds_or,!pathpop_holds_equal,!pathpop_eval_up,code_eval_num;exact Hb.
   +rewrite holds_and,!pathpop_holds_equal,pathpop_eval_add,pathpop_eval_mul,
      !pathpop_eval_up,pathpop_eval_succ,code_eval_num;exact Hr. }
 rewrite Htail. rewrite(holds_and M rho(code==num 1)((head==zero) ∧(rest==num 1))),
   (holds_and M rho(head==zero)(rest==num 1)),!pathpop_holds_equal,!code_eval_num;reflexivity.
Qed.

Section Pop.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring program230_pop_ring:(model_semiring M).
Lemma program230_path_pop_cons_not_one h rest:
 machine230_is_bit M h->(exists k,rest=S k)->h+two*rest<>one.
Proof.
 intros Hb[k Hrest]E.
 assert(Eword:two*rest+h=two*Z+one).
 {transitivity(succM M Z);[rewrite Arithmetic.add_comm;exact E|ring]. }
 destruct(machine230_pop_unique M h rest one Z Hb(or_intror eq_refl)Eword)as[_ Hr].
 rewrite Hrest in Hr;apply(zero_ne_succ M k);now symmetry.
Qed.
Theorem program230_path_pop_total code:code<>Z->exists h rest,program230_path_pop M code h rest.
Proof.
 intro Hnz. destruct(machine230_pop_total M code)as[h[rest[Hb E]]].
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
   (fun ax H rho=>axioms M ax rho H)rest)as[Hr|[k Hr]].
 -change(code=two*rest+h)in E.
  change(rest=Z)in Hr. rewrite Hr in E.
  assert(Eh:code=h)by(rewrite E;ring).
  unfold machine230_is_bit in Hb. destruct Hb as[Hb|Hb].
  +exfalso;apply Hnz;rewrite Eh;exact Hb.
  +exists Z,one;left;split;[rewrite Eh;exact Hb|auto].
 -exists h,rest;right;split;[exact Hb|exists k;split;[exact Hr|]].
  change(code=two*rest+h)in E. change(code=h+two*rest). rewrite E;ring.
Qed.
Theorem program230_path_pop_unique code h r h' r':
 program230_path_pop M code h r->program230_path_pop M code h' r'->h=h' /\r=r'.
Proof.
 intros[[Ec[Eh Er]]|[Hb[k[Er Ec]]]][[Fc[Fh Fr]]|[Hc[j[Fr Fc]]]].
 -split;congruence.
 -exfalso;apply(program230_path_pop_cons_not_one h' r' Hc);[exists j;exact Fr|].
  change(code=h'+two*r')in Fc. rewrite <-Fc;exact Ec.
 -exfalso;apply(program230_path_pop_cons_not_one h r Hb);[exists k;exact Er|].
  change(code=h+two*r)in Ec. rewrite <-Ec;exact Fc.
 -apply(machine230_pop_unique M h r h' r' Hb Hc).
  change(code=h+two*r)in Ec. change(code=h'+two*r')in Fc.
  transitivity(code);[rewrite Arithmetic.add_comm;now symmetry|rewrite Arithmetic.add_comm;exact Fc].
Qed.
Theorem program230_path_pop_list P:
 program230_path_pop M(program230_path_value M P)
  (machine230_bitM M(hd false P))(program230_path_value M(tl P)).
Proof.
 destruct P as[|b P].
 -left;repeat split;reflexivity.
 -right;split;[apply machine230_bit_is_bit|].
  destruct(program230_path_successor M P)as[k Hk];exists k;split;[exact Hk|reflexivity].
Qed.
End Pop.
Print Assumptions program230_path_pop_formula_correct.
Print Assumptions program230_path_pop_total.
Print Assumptions program230_path_pop_unique.
Print Assumptions program230_path_pop_list.
