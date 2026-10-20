(** Compact, length-sensitive codes for the public register program's paths.
    The terminating one is a coding sentinel, separate from the tape marker. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions TM230LiteralActions
 TM230BitArithmetic.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Bool.Bool setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint program230_path_value M(P:list bool):carrier M:=
 match P with
 |[]=>succM M(zeroM M)
 |b::P=>addM M(machine230_bitM M b)
   (mulM M(code_numeral M 2)(program230_path_value M P))
 end.
Fixpoint program230_path_term(P:list bool):term:=
 match P with
 |[]=>num 1
 |b::P=>num(machine230_bit b)⊕num 2⊗program230_path_term P
 end.
Lemma program230_path_term_correct M rho P:
 evalM M rho(program230_path_term P)=program230_path_value M P.
Proof.
 induction P as[|b P IH];[reflexivity|].
 change(addM M(evalM M rho(num(machine230_bit b)))
  (mulM M(evalM M rho(num 2))(evalM M rho(program230_path_term P)))=
  addM M(machine230_bitM M b)(mulM M(code_numeral M 2)(program230_path_value M P))).
 rewrite !code_eval_num,IH;reflexivity.
Qed.

Section Faithful.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring program230_path_ring:(model_semiring M).

Lemma program230_path_successor P:exists k,program230_path_value M P=S k.
Proof.
 induction P as[|b P[k Hk]].
 -exists Z;reflexivity.
 -cbn[program230_path_value];rewrite Hk;destruct b.
  +exists(S(S(two*k))).
   change(one+two*S k=S(S(S(two*k)))).
   rewrite(succ_as_add M k),(succ_as_add M(S(S(two*k)))),
    (succ_as_add M(S(two*k))),(succ_as_add M(two*k)),(succ_as_add M one);ring.
  +exists(S(two*k)).
   change(Z+two*S k=S(S(two*k))).
   rewrite(succ_as_add M k),(succ_as_add M(S(two*k))),
    (succ_as_add M(two*k)),(succ_as_add M one);ring.
Qed.
Lemma program230_path_nonzero P:program230_path_value M P<>Z.
Proof. destruct(program230_path_successor P)as[k ->];intro H;exact(zero_ne_succ M k(eq_sym H)). Qed.
Lemma program230_path_nonempty b P:program230_path_value M(b::P)<>one.
Proof.
 intro H. assert(Eword:two*program230_path_value M P+machine230_bitM M b=two*Z+one).
 {change(two*program230_path_value M P+machine230_bitM M b=two*Z+one).
  change(machine230_bitM M b+two*program230_path_value M P=one)in H.
  transitivity(succM M Z);[rewrite Arithmetic.add_comm;exact H|ring]. }
 destruct(machine230_pop_unique M(machine230_bitM M b)(program230_path_value M P)one Z
   (machine230_bit_is_bit M b)(or_intror eq_refl)Eword)as[_ E].
 exact(program230_path_nonzero P E).
Qed.
Lemma program230_bitM_injective b c:machine230_bitM M b=machine230_bitM M c->b=c.
Proof.
 destruct b,c;intro H;try reflexivity.
 -exfalso;exact(zero_ne_succ M Z(eq_sym H)).
 -exfalso;exact(zero_ne_succ M Z H).
Qed.
Theorem program230_path_value_injective P Q:
 program230_path_value M P=program230_path_value M Q->P=Q.
Proof.
 induction P as[|b P IH]in Q|-*;destruct Q as[|c Q];intro H.
 -reflexivity.
 -exfalso;apply(program230_path_nonempty c Q);symmetry;exact H.
 -exfalso;apply(program230_path_nonempty b P);exact H.
 -assert(Eword:two*program230_path_value M P+machine230_bitM M b=
    two*program230_path_value M Q+machine230_bitM M c).
  {change(machine230_bitM M b+two*program230_path_value M P=
     machine230_bitM M c+two*program230_path_value M Q)in H.
   etransitivity;[apply Arithmetic.add_comm|].
   etransitivity;[exact H|apply Arithmetic.add_comm]. }
  destruct(machine230_pop_unique M(machine230_bitM M b)(program230_path_value M P)
    (machine230_bitM M c)(program230_path_value M Q)
    (machine230_bit_is_bit M b)(machine230_bit_is_bit M c)Eword)as[Eb EP].
  apply program230_bitM_injective in Eb;subst c. f_equal;now apply IH.
Qed.
End Faithful.
Print Assumptions program230_path_term_correct.
Print Assumptions program230_path_value_injective.
