(** Prefix uniqueness of arbitrary internally coded literal-machine histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs PowerTwoSyntax
 TM230RegisterWords TM230BinaryStep TM230RunArithmetic TM230StandardRun TM230StandardPacking TM230RunComposition TM230Paths TM230ExactPaths TM230StepDeterminism.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition machine230_prefix_unique_at M b c n d e k i:=
 coding_lt M i(succM M n)->coding_lt M i(succM M k)->forall s t,
 machine230_state_at M b c i s ->machine230_state_at M d e i t ->s=t.
Definition machine230_prefix_unique_formula:form:=
 Peano.sless $0(σ $1)→Peano.sless $0(σ $2)→∀∀∀∀∀∀∀∀
 (machine230_state_at_formula $11 $12 $8 $7 $6 $5 $4 →
 machine230_state_at_formula $13 $14 $8 $3 $2 $1 $0 →
 ($7==$3 ∧($6==$2 ∧($5==$1 ∧$4==$0)))).
Local Opaque holds Peano.sless machine230_state_at_formula.
Lemma machine230_prefix_unique_definable M b c n d e k:
 Definable1 M(machine230_prefix_unique_at M b c n d e k).
Proof.
 exists machine230_prefix_unique_formula,(n.:k.:b.:c.:d.:e.:(fun _=>zeroM M)). intro i.
 unfold machine230_prefix_unique_formula,machine230_prefix_unique_at.
 repeat setoid_rewrite holds_imp. repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 repeat setoid_rewrite holds_and. setoid_rewrite less_formula_correct.
 setoid_rewrite machine230_state_at_formula_correct. setoid_rewrite power_holds_equal.
 setoid_rewrite register_eval_succ. cbn[evalM]. split.
 -intros H Hn Hk sq sl sh sr tq tl th tr HS HT.
  specialize(H Hn Hk(machine230_mk_config(carrier M)sq sl sh sr)
   (machine230_mk_config(carrier M)tq tl th tr)HS HT).
  injection H as Eq El Eh Er. auto.
 -intros H Hn Hk[sq sl sh sr][tq tl th tr]HS HT.
  specialize(H Hn Hk sq sl sh sr tq tl th tr HS HT). destruct H as[Eq[El[Eh Er]]].
  change(sq=tq)in Eq. change(sl=tl)in El. change(sh=th)in Eh. change(sr=tr)in Er. now subst.
Qed.
Theorem machine230_run_prefix_unique M b c n d e k start:
 machine230_run_from M b c n start ->machine230_run_from M d e k start ->
 forall i,machine230_prefix_unique_at M b c n d e k i.
Proof.
 intros[HS HR][HS' HR'].
 apply(definable_induction M(machine230_prefix_unique_at M b c n d e k)
  (machine230_prefix_unique_definable M b c n d e k)).
 -intros Hn Hk s t Hs Ht.
  assert(Es:s=start)by(eapply machine230_state_at_unique;eassumption).
  assert(Et:t=start)by(eapply machine230_state_at_unique;eassumption). congruence.
 -intros i IH Hn Hk s t Hs Ht.
  assert(Hin:coding_lt M i n)by(now apply coding_lt_succ_cancel).
  assert(Hik:coding_lt M i k)by(now apply coding_lt_succ_cancel).
  destruct(machine230_state_at_total M b c i)as[previous HP].
  destruct(machine230_state_at_total M d e i)as[previous' HP'].
  assert(E:previous=previous').
  {apply IH;[apply coding_lt_succ_cases;now left|apply coding_lt_succ_cases;now left|exact HP|exact HP']. }
  subst previous'. exact(machine230_step_functional M previous s t(HR i previous s Hin HP Hs)(HR' i previous t Hik HP' Ht)).
Qed.
Theorem machine230_path_endpoint_unique M b c d e n start first second:
 machine230_path M b c n start first ->machine230_path M d e n start second ->first=second.
Proof.
 intros[HR HE][HR' HE'].
 exact(machine230_run_prefix_unique M b c n d e n start HR HR' n(coding_lt_succ M n)(coding_lt_succ M n)first second HE HE').
Qed.
Theorem machine230_reaches_in_functional M n start first second:
 machine230_reaches_in M n start first ->machine230_reaches_in M n start second ->first=second.
Proof.
 intros[b[c H]][d[e H']]. exact(machine230_path_endpoint_unique M b c d e n start first second H H').
Qed.
Print Assumptions machine230_run_prefix_unique.
Print Assumptions machine230_path_endpoint_unique.
Print Assumptions machine230_reaches_in_functional.
