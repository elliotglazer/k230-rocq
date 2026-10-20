(** Reachability with the exact internally coded transition count retained. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 TM230BinaryStep TM230RunArithmetic TM230StandardPacking TM230RunComposition TM230Paths.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
Definition machine230_reaches_in M n s t:=exists b c,machine230_path M b c n s t.
Definition machine230_reaches_in_formula n q l h r q' l' h' r':form:=
 ∃∃machine230_path_formula $1 $0(code_lift2 n)
 (code_lift2 q)(code_lift2 l)(code_lift2 h)(code_lift2 r)
 (code_lift2 q')(code_lift2 l')(code_lift2 h')(code_lift2 r').
Local Opaque holds machine230_path_formula.
Lemma machine230_reaches_in_formula_correct M rho n q l h r q' l' h' r':
 holds M rho(machine230_reaches_in_formula n q l h r q' l' h' r') <->
 machine230_reaches_in M(evalM M rho n)
 (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r))
 (machine230_mk_config(carrier M)(evalM M rho q')(evalM M rho l')(evalM M rho h')(evalM M rho r')).
Proof.
 unfold machine230_reaches_in_formula,machine230_reaches_in.
 repeat setoid_rewrite holds_ex. setoid_rewrite machine230_path_formula_correct.
 repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Lemma machine230_reaches_in_zero M s:machine230_reaches_in M(zeroM M)s s.
Proof. apply machine230_path_zero. Qed.
Lemma machine230_reaches_in_one M s t:machine230_step M s t->
 machine230_reaches_in M(succM M(zeroM M))s t.
Proof. apply machine230_path_one. Qed.
Lemma machine230_reaches_in_join M n k s u t:
 machine230_reaches_in M n s u ->machine230_reaches_in M k u t ->
 machine230_reaches_in M(addM M n k)s t.
Proof.
 intros[b[c H1]][d[e H2]]. exact(machine230_path_join M b c n d e k s u t H1 H2).
Qed.
Lemma machine230_reaches_in_step M s u t n:machine230_step M s u ->
 machine230_reaches_in M n u t ->machine230_reaches_in M(succM M n)s t.
Proof.
 intros Hstep Hrest. pose proof(machine230_reaches_in_join M _ n s u t
  (machine230_reaches_in_one M s u Hstep)Hrest)as H.
 change(machine230_reaches_in M(addM M(succM M(zeroM M))n)s t)in H.
 now rewrite Arithmetic.add_succ,Arithmetic.add_zero in H.
Qed.
Print Assumptions machine230_reaches_in_formula_correct.
Print Assumptions machine230_reaches_in_step.
