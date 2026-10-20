(** Fixed finite reads of an internally valued instruction pointer. Every read
    uses the exact implicit-zero sentinel convention and has an ordinary PA
    graph. No numerical instruction pointer is converted to a unary numeral. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 NumericalProofs TM230LiteralActions TM230BitArithmetic Program230PathCode Program230PathPop.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint program230_read M code (bits:list bool) rest:Prop:=
 match bits with
 |[]=>code=rest
 |b::bits=>exists next,
    program230_path_pop M code(machine230_bitM M b)next /\
    program230_read M next bits rest
 end.

Fixpoint program230_read_formula(code:term)(bits:list bool)(rest:term):form:=
 match bits with
 |[]=>code==rest
 |b::bits=>
   ∃(program230_path_pop_formula code`[↑](num(machine230_bit b)) $0 ∧
      program230_read_formula $0 bits rest`[↑])
 end.

Theorem program230_read_formula_correct M bits rho code rest:
 holds M rho(program230_read_formula code bits rest)<->
 program230_read M(evalM M rho code)bits(evalM M rho rest).
Proof.
 induction bits as[|b bits IH]in rho,code,rest|-*.
 -reflexivity.
 -cbn[program230_read_formula program230_read]. rewrite holds_ex.
  assert(Hbody:forall x,
   holds M(x.:rho)(program230_path_pop_formula code`[↑](num(machine230_bit b)) $0 ∧
    program230_read_formula $0 bits rest`[↑])<->
   program230_path_pop M(evalM M rho code)(machine230_bitM M b)x /\
    program230_read M x bits(evalM M rho rest)).
  {intro x.
   rewrite(holds_and M(x.:rho)
     (program230_path_pop_formula code`[↑](num(machine230_bit b)) $0)
     (program230_read_formula $0 bits rest`[↑])),program230_path_pop_formula_correct,IH,
     !pathpop_eval_up,code_eval_num;reflexivity. }
  setoid_rewrite Hbody;reflexivity.
Qed.

Lemma program230_pop_head_bit M code h rest:
 program230_path_pop M code h rest->machine230_is_bit M h.
Proof.
 intros[[Hc[-> Hr]]|[Hb Hrest]];[left;reflexivity|exact Hb].
Qed.
Lemma program230_pop_rest_nonzero M code h rest:
 program230_path_pop M code h rest->rest<>zeroM M.
Proof.
 intros[[Hc[Hh ->]]|[Hb[k[-> Hc]]]]H.
 -apply(zero_ne_succ M(zeroM M));now symmetry.
 -apply(zero_ne_succ M k);now symmetry.
Qed.

Theorem program230_read_total M n code:
 code<>zeroM M->exists bits rest,
  length bits=n /\program230_read M code bits rest /\rest<>zeroM M.
Proof.
 induction n as[|n IH]in code|-*;intro Hnz.
 -exists[],code;repeat split;auto.
 -destruct(program230_path_pop_total M code Hnz)as[h[next Hpop]].
  pose proof(program230_pop_head_bit M code h next Hpop)as Hb.
  pose proof(program230_pop_rest_nonzero M code h next Hpop)as Hnext.
  destruct(IH next Hnext)as[bits[rest[Hlen[Hread Hr]]]].
  destruct Hb as[Hh|Hh].
  +exists(false::bits),rest;split;[cbn;now rewrite Hlen|split;[|exact Hr]].
   exists next;split;[change(program230_path_pop M code(zeroM M)next);now rewrite <-Hh|exact Hread].
  +exists(true::bits),rest;split;[cbn;now rewrite Hlen|split;[|exact Hr]].
   exists next;split;[change(program230_path_pop M code(succM M(zeroM M))next);now rewrite <-Hh|exact Hread].
Qed.

Theorem program230_read_deterministic M bits code rest bits' rest':
 program230_read M code bits rest->program230_read M code bits' rest'->
 length bits=length bits'->bits=bits' /\rest=rest'.
Proof.
 induction bits as[|b bits IH]in code,rest,bits',rest'|-*;
  destruct bits' as[|b' bits'];cbn[program230_read];intros H K Hlen;try discriminate.
 -split;[reflexivity|congruence].
 -destruct H as[next[Hpop Hread]],K as[next'[Kpop Kread]].
  destruct(program230_path_pop_unique M code(machine230_bitM M b)next
    (machine230_bitM M b')next' Hpop Kpop)as[Hbit Hnext].
  apply program230_bitM_injective in Hbit;subst b' next'.
  apply Nat.succ_inj in Hlen.
  destruct(IH next rest bits' rest' Hread Kread Hlen)as[Hbits Hr].
  subst bits';split;[reflexivity|exact Hr].
Qed.

Fixpoint program230_take_zeros n(P:list bool):list bool:=
 match n with 0=>[]|S n=>hd false P::program230_take_zeros n(tl P)end.
Lemma program230_take_zeros_length n P:length(program230_take_zeros n P)=n.
Proof. induction n as[|n IH]in P|-*;cbn;[reflexivity|now rewrite IH]. Qed.
Lemma program230_firstn_repeat n m(b:bool):
 (n<=m)%nat->firstn n(repeat b m)=repeat b n.
Proof.
 induction n as[|n IH]in m|-*;destruct m;intro H;cbn;try reflexivity;try lia.
 f_equal;apply IH;lia.
Qed.
Lemma program230_take_zeros_source_prefix n P:
 program230_take_zeros n P=firstn n(P++repeat false n).
Proof.
 induction n as[|n IH]in P|-*;[reflexivity|].
 destruct P as[|b P];cbn[program230_take_zeros firstn hd tl app repeat].
 -rewrite IH;cbn[app]. rewrite firstn_all2;[reflexivity|rewrite repeat_length;lia].
 -rewrite IH. f_equal. rewrite !firstn_app. f_equal.
  change(firstn(n-length P)(repeat false n)=firstn(n-length P)(repeat false(S n))).
  rewrite !program230_firstn_repeat;try lia;reflexivity.
Qed.

Theorem program230_read_path M n P:
 program230_read M(program230_path_value M P)(program230_take_zeros n P)
  (program230_path_value M(skipn n P)).
Proof.
 induction n as[|n IH]in P|-*;[reflexivity|].
 cbn[program230_take_zeros program230_read].
 exists(program230_path_value M(tl P));split;[apply program230_path_pop_list|].
 destruct P as[|b P];cbn[tl skipn].
 -specialize(IH (@nil bool));now rewrite skipn_nil in IH.
 -exact(IH P).
Qed.

Print Assumptions program230_read_formula_correct.
Print Assumptions program230_read_total.
Print Assumptions program230_read_deterministic.
Print Assumptions program230_take_zeros_source_prefix.
Print Assumptions program230_read_path.
