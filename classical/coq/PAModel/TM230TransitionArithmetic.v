(** Literal finite transition relation, interpreted arithmetically in every PA model. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions StandardModel NumericalProofs TM230LiteralActions.
From FOL Require Import FullSyntax Arithmetics.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
#[local] Existing Instance falsity_on |0.
Definition machine230_action_relation M(a:machine230_action)(q r w d n:carrier M):Prop :=
 let '(qa,ra,wa,da,na):=a in
 q=code_numeral M qa /\r=code_numeral M(machine230_bit ra) /\
 w=code_numeral M(machine230_bit wa) /\d=code_numeral M(machine230_direction da) /\n=code_numeral M na.
Definition machine230_action_formula(a:machine230_action)(q r w d n:term):form :=
 let '(qa,ra,wa,da,na):=a in
 q==num qa ∧(r==num(machine230_bit ra) ∧
 (w==num(machine230_bit wa) ∧(d==num(machine230_direction da) ∧n==num na))).
Fixpoint machine230_rows_formula(rows:list machine230_action)(q r w d n:term):form :=
 match rows with
 |[]=>⊥
 |a::rest=>machine230_action_formula a q r w d n ∨machine230_rows_formula rest q r w d n
 end.
Definition machine230_transition M(q r w d n:carrier M):Prop :=
 exists a,In a machine230_actions /\machine230_action_relation M a q r w d n.
Definition machine230_transition_formula(q r w d n:term):form :=
 machine230_rows_formula machine230_actions q r w d n.
Lemma machine230_action_formula_correct M rho a q r w d n:
 holds M rho(machine230_action_formula a q r w d n)<->
 machine230_action_relation M a(evalM M rho q)(evalM M rho r)(evalM M rho w)(evalM M rho d)(evalM M rho n).
Proof.
 destruct a as [[[[qa ra]wa]da]na]. unfold machine230_action_formula,machine230_action_relation.
 rewrite !holds_and.
 change((evalM M rho q=evalM M rho(num qa) /\evalM M rho r=evalM M rho(num(machine230_bit ra)) /\
  evalM M rho w=evalM M rho(num(machine230_bit wa)) /\evalM M rho d=evalM M rho(num(machine230_direction da)) /\
  evalM M rho n=evalM M rho(num na))<->
 (evalM M rho q=code_numeral M qa /\evalM M rho r=code_numeral M(machine230_bit ra) /\
 evalM M rho w=code_numeral M(machine230_bit wa) /\evalM M rho d=code_numeral M(machine230_direction da) /\evalM M rho n=code_numeral M na)).
 now rewrite !code_eval_num.
Qed.
Lemma machine230_rows_formula_correct M rho rows q r w d n:
 holds M rho(machine230_rows_formula rows q r w d n)<->
 exists a,In a rows /\machine230_action_relation M a(evalM M rho q)(evalM M rho r)(evalM M rho w)(evalM M rho d)(evalM M rho n).
Proof.
 induction rows as[|a rows IH].
 -change(False<->exists a,In a (@nil machine230_action) /\machine230_action_relation M a(evalM M rho q)(evalM M rho r)(evalM M rho w)(evalM M rho d)(evalM M rho n)). firstorder.
 -cbn[machine230_rows_formula]. rewrite holds_or,machine230_action_formula_correct,IH.
  split.
  +intros[H|(x&Hx&HR)];[exists a|exists x];cbn;auto.
  +intros(x&[<-|H]&HR);[now left|right;exists x;auto].
Qed.
Theorem machine230_transition_formula_correct M rho q r w d n:
 holds M rho(machine230_transition_formula q r w d n)<->
 machine230_transition M(evalM M rho q)(evalM M rho r)(evalM M rho w)(evalM M rho d)(evalM M rho n).
Proof. apply machine230_rows_formula_correct. Qed.
Lemma machine230_action_nat_exact a q b w d n:
 machine230_action_relation natModel a q(machine230_bit b)(machine230_bit w)(machine230_direction d)n<->
 a=(q,b,w,d,n).
Proof.
 destruct a as [[[[qa ba]wa]da]na]. unfold machine230_action_relation.
 rewrite !numeral_natModel. split.
 -intros(Hq&Hb&Hw&Hd&Hn). apply machine230_bit_injective in Hb,Hw.
  apply machine230_direction_injective in Hd. subst. reflexivity.
 -intro H. inversion H;subst;repeat split;reflexivity.
Qed.
Theorem machine230_transition_nat_exact q b w d n:
 machine230_transition natModel q(machine230_bit b)(machine230_bit w)(machine230_direction d)n<->
 Public230.tmn q b=Some(w,d,n).
Proof.
 unfold machine230_transition. setoid_rewrite machine230_action_nat_exact.
 rewrite <-machine230_action_exact. split.
 -intros(a&Ha&->). exact Ha.
 -intro H. exists(q,b,w,d,n). auto.
Qed.
Print Assumptions machine230_transition_formula_correct.
Print Assumptions machine230_transition_nat_exact.
