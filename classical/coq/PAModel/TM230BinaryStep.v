(** A concrete four-number tape representation. Both half-tapes have their
    nearest cell in the least significant binary digit. No bounded-time
    correspondence with the register machine is assumed here. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs TM230TransitionArithmetic.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
#[local] Existing Instance falsity_on |0.
Record machine230_config(A:Type):=machine230_mk_config{
 machine230_state:A;machine230_left:A;machine230_head:A;machine230_right:A}.
Arguments machine230_state{A}_ .
Arguments machine230_left{A}_ .
Arguments machine230_head{A}_ .
Arguments machine230_right{A}_ .
Definition machine230_seed M:=machine230_mk_config(carrier M)(zeroM M)(zeroM M)(zeroM M)(zeroM M).
Definition machine230_step M(a b:machine230_config(carrier M)):Prop :=
 exists w d,
 machine230_transition M(machine230_state a)(machine230_head a)w d(machine230_state b) /\
 (machine230_head b=zeroM M \/machine230_head b=code_numeral M 1) /\
 ((d=zeroM M /\
   machine230_right b=addM M(mulM M(code_numeral M 2)(machine230_right a))w /\
   machine230_left a=addM M(mulM M(code_numeral M 2)(machine230_left b))(machine230_head b)) \/
  (d=code_numeral M 1 /\
   machine230_left b=addM M(mulM M(code_numeral M 2)(machine230_left a))w /\
   machine230_right a=addM M(mulM M(code_numeral M 2)(machine230_right b))(machine230_head b))).
Definition machine230_step_formula(q l h r q' l' h' r':term):form :=
 ∃∃(machine230_transition_formula(code_lift2 q)(code_lift2 h)$1 $0(code_lift2 q') ∧
 ((code_lift2 h'==zero ∨code_lift2 h'==num 1) ∧
 (($0==zero ∧(code_lift2 r'==((num 2⊗code_lift2 r)⊕$1) ∧
               code_lift2 l==((num 2⊗code_lift2 l')⊕code_lift2 h'))) ∨
  ($0==num 1 ∧(code_lift2 l'==((num 2⊗code_lift2 l)⊕$1) ∧
                code_lift2 r==((num 2⊗code_lift2 r')⊕code_lift2 h')))))).
Lemma machine230_holds_equal M rho t u:
 holds M rho(t==u)<->evalM M rho t=evalM M rho u.
Proof. reflexivity. Qed.
Lemma machine230_eval_add M rho t u:
 evalM M rho(t⊕u)=addM M(evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Lemma machine230_eval_mul M rho t u:
 evalM M rho(t⊗u)=mulM M(evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Local Opaque machine230_transition_formula holds.
Theorem machine230_step_formula_correct M rho q l h r q' l' h' r':
 holds M rho(machine230_step_formula q l h r q' l' h' r')<->
 machine230_step M
 (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r))
 (machine230_mk_config(carrier M)(evalM M rho q')(evalM M rho l')(evalM M rho h')(evalM M rho r')).
Proof.
 unfold machine230_step_formula,machine230_step.
 repeat setoid_rewrite holds_ex.
 repeat first [progress(setoid_rewrite holds_and)|progress(setoid_rewrite holds_or)].
 setoid_rewrite machine230_transition_formula_correct.
 repeat setoid_rewrite machine230_holds_equal.
 repeat setoid_rewrite machine230_eval_add. repeat setoid_rewrite machine230_eval_mul.
 repeat setoid_rewrite code_eval_lift2. repeat setoid_rewrite code_eval_num.
 reflexivity.
Qed.
Print Assumptions machine230_step_formula_correct.
