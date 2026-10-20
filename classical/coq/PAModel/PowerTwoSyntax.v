(** Powers of two by a beta-coded recurrence of arbitrary internal length. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 CodeExpressions NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition power2_trace M b c n :=
 beta M b c(zeroM M)(code_numeral M 1) /\
 forall i,coding_lt M i n ->forall x y,beta M b c i x ->
  beta M b c(succM M i)y ->y=mulM M(code_numeral M 2)x.
Definition power2 M n p :=exists b c,power2_trace M b c n /\beta M b c n p.
Definition power_lift3(t:term):term:=t`[↑]`[↑]`[↑].
Definition power2_trace_formula(b c n:term):form:=
 beta_formula b c zero(num 1) ∧∀∀∀
 ((Peano.sless $2(power_lift3 n) ∧
   beta_formula(power_lift3 b)(power_lift3 c)$2 $1 ∧
   beta_formula(power_lift3 b)(power_lift3 c)(σ $2)$0) →
  $0 == num 2 ⊗ $1).
Definition power2_formula(n p:term):form:=∃∃
 (power2_trace_formula $1 $0(code_lift2 n) ∧
  beta_formula $1 $0(code_lift2 n)(code_lift2 p)).
Lemma power_lift3_eval M rho x y z t:
 evalM M(z .:y .:x .:rho)(power_lift3 t)=evalM M rho t.
Proof. unfold evalM,power_lift3;now rewrite !eval_up. Qed.
Lemma power_holds_equal M rho a b:holds M rho(a==b)<->evalM M rho a=evalM M rho b.
Proof. reflexivity. Qed.
Local Opaque holds beta_formula Peano.sless.
Lemma power2_trace_formula_correct M rho b c n:
 holds M rho(power2_trace_formula b c n)<->
 power2_trace M(evalM M rho b)(evalM M rho c)(evalM M rho n).
Proof.
 unfold power2_trace_formula,power2_trace. rewrite holds_and,beta_formula_correct.
 repeat setoid_rewrite holds_all. setoid_rewrite holds_imp.
 repeat setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
 setoid_rewrite less_formula_correct. setoid_rewrite power_lift3_eval.
 setoid_rewrite power_holds_equal.
 change((beta M(evalM M rho b)(evalM M rho c)(zeroM M)(code_numeral M 1) /\
  forall i x y,((coding_lt M i(evalM M rho n) /\
    beta M(evalM M rho b)(evalM M rho c)i x) /\
    beta M(evalM M rho b)(evalM M rho c)(succM M i)y)->
    y=mulM M(code_numeral M 2)x)<-> power2_trace M(evalM M rho b)(evalM M rho c)(evalM M rho n)).
 split;intros[H0 H];split;[exact H0| |exact H0|].
 - intros i Hi x y Hx Hy. apply(H i x y). auto.
 - intros i x y[[Hi Hx]Hy]. exact(H i Hi x y Hx Hy).
Qed.
Lemma power2_formula_correct M rho n p:
 holds M rho(power2_formula n p)<->power2 M(evalM M rho n)(evalM M rho p).
Proof.
 unfold power2_formula,power2. repeat setoid_rewrite holds_ex.
 setoid_rewrite holds_and. setoid_rewrite power2_trace_formula_correct.
 setoid_rewrite beta_formula_correct. repeat setoid_rewrite code_eval_lift2.
 reflexivity.
Qed.
Definition power2_exists M n:=exists p,power2 M n p.
Lemma power2_exists_definable M:Definable1 M(power2_exists M).
Proof.
 exists(∃power2_formula $1 $0),(fun _=>zeroM M). intro n.
 change((exists p,power2 M n p)<->holds M(n .:(fun _=>zeroM M))(∃power2_formula $1 $0)).
 rewrite holds_ex. setoid_rewrite power2_formula_correct. reflexivity.
Qed.
Definition power2_unique_at M n:=forall p q,power2 M n p->power2 M n q->p=q.
Lemma power2_unique_definable M:Definable1 M(power2_unique_at M).
Proof.
 exists(∀∀(power2_formula $2 $1→power2_formula $2 $0→$1==$0)),(fun _=>zeroM M).
 intro n. unfold power2_unique_at. repeat setoid_rewrite holds_all.
 repeat setoid_rewrite holds_imp. repeat setoid_rewrite power2_formula_correct.
 setoid_rewrite power_holds_equal.
 reflexivity.
Qed.
Print Assumptions power2_formula_correct.
Print Assumptions power2_exists_definable.
Print Assumptions power2_unique_definable.
