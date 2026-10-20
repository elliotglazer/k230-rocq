(** The exact spare-file word: E identical false/true/true blocks. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 CodeExpressions NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition machine230_spare_trace M b c n :=
 beta M b c(zeroM M)(zeroM M) /\
 forall i,coding_lt M i n ->forall x y,beta M b c i x ->
  beta M b c(succM M i)y ->y=addM M(code_numeral M 6)(mulM M(code_numeral M 8)x).
Definition machine230_spare M n p :=exists b c,machine230_spare_trace M b c n /\beta M b c n p.
Definition spare_lift3(t:term):term:=t`[↑]`[↑]`[↑].
Definition machine230_spare_trace_formula(b c n:term):form:=
 beta_formula b c zero zero ∧∀∀∀
 ((Peano.sless $2(spare_lift3 n) ∧
   beta_formula(spare_lift3 b)(spare_lift3 c)$2 $1 ∧
   beta_formula(spare_lift3 b)(spare_lift3 c)(σ $2)$0) →
  $0 == num 6 ⊕num 8 ⊗ $1).
Definition machine230_spare_formula(n p:term):form:=∃∃
 (machine230_spare_trace_formula $1 $0(code_lift2 n) ∧
  beta_formula $1 $0(code_lift2 n)(code_lift2 p)).
Lemma spare_lift3_eval M rho x y z t:
 evalM M(z .:y .:x .:rho)(spare_lift3 t)=evalM M rho t.
Proof. unfold evalM,spare_lift3;now rewrite !eval_up. Qed.
Lemma spare_holds_equal M rho a b:holds M rho(a==b)<->evalM M rho a=evalM M rho b.
Proof. reflexivity. Qed.
Local Opaque holds beta_formula Peano.sless.
Lemma machine230_spare_trace_formula_correct M rho b c n:
 holds M rho(machine230_spare_trace_formula b c n)<->
 machine230_spare_trace M(evalM M rho b)(evalM M rho c)(evalM M rho n).
Proof.
 unfold machine230_spare_trace_formula,machine230_spare_trace. rewrite holds_and,beta_formula_correct.
 repeat setoid_rewrite holds_all. setoid_rewrite holds_imp.
 repeat setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
 setoid_rewrite less_formula_correct. setoid_rewrite spare_lift3_eval.
 setoid_rewrite spare_holds_equal.
 change((beta M(evalM M rho b)(evalM M rho c)(zeroM M)(zeroM M) /\
  forall i x y,((coding_lt M i(evalM M rho n) /\
    beta M(evalM M rho b)(evalM M rho c)i x) /\
    beta M(evalM M rho b)(evalM M rho c)(succM M i)y)->
    y=addM M(code_numeral M 6)(mulM M(code_numeral M 8)x))<-> machine230_spare_trace M(evalM M rho b)(evalM M rho c)(evalM M rho n)).
 split;intros[H0 H];split;[exact H0| |exact H0|].
 - intros i Hi x y Hx Hy. apply(H i x y). auto.
 - intros i x y[[Hi Hx]Hy]. exact(H i Hi x y Hx Hy).
Qed.
Lemma machine230_spare_formula_correct M rho n p:
 holds M rho(machine230_spare_formula n p)<->machine230_spare M(evalM M rho n)(evalM M rho p).
Proof.
 unfold machine230_spare_formula,machine230_spare. repeat setoid_rewrite holds_ex.
 setoid_rewrite holds_and. setoid_rewrite machine230_spare_trace_formula_correct.
 setoid_rewrite beta_formula_correct. repeat setoid_rewrite code_eval_lift2.
 reflexivity.
Qed.
Definition machine230_spare_exists M n:=exists p,machine230_spare M n p.
Lemma machine230_spare_exists_definable M:Definable1 M(machine230_spare_exists M).
Proof.
 exists(∃machine230_spare_formula $1 $0),(fun _=>zeroM M). intro n.
 change((exists p,machine230_spare M n p)<->holds M(n .:(fun _=>zeroM M))(∃machine230_spare_formula $1 $0)).
 rewrite holds_ex. setoid_rewrite machine230_spare_formula_correct. reflexivity.
Qed.
Definition machine230_spare_unique_at M n:=forall p q,machine230_spare M n p->machine230_spare M n q->p=q.
Lemma machine230_spare_unique_definable M:Definable1 M(machine230_spare_unique_at M).
Proof.
 exists(∀∀(machine230_spare_formula $2 $1→machine230_spare_formula $2 $0→$1==$0)),(fun _=>zeroM M).
 intro n. unfold machine230_spare_unique_at. repeat setoid_rewrite holds_all.
 repeat setoid_rewrite holds_imp. repeat setoid_rewrite machine230_spare_formula_correct.
 setoid_rewrite spare_holds_equal.
 reflexivity.
Qed.
Print Assumptions machine230_spare_formula_correct.
Print Assumptions machine230_spare_exists_definable.
Print Assumptions machine230_spare_unique_definable.
