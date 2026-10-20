(** Internally indexed register blocks and the exact carry-induction property. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 PowerTwoSyntax TM230UnaryBlocks TM230RegisterWords TM230BinaryStep TM230BitArithmetic
 TM230Paths TM230ExactPaths.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition machine230_carry_chain M vb vc wb wc count:=forall i,coding_lt M i count->
 exists v w next,beta M vb vc i v /\beta M wb wc i w /\
 beta M wb wc(succM M i)next /\machine230_unary_block M v next w.
Definition machine230_carry_chain_formula(vb vc wb wc count:term):form:=
 ∀(Peano.sless $0 count`[↑] →∃∃∃
 (beta_formula(code_lift4 vb)(code_lift4 vc)$3 $2 ∧
 (beta_formula(code_lift4 wb)(code_lift4 wc)$3 $1 ∧
 (beta_formula(code_lift4 wb)(code_lift4 wc)(σ $3)$0 ∧
 machine230_unary_block_formula $2 $0 $1)))).
Definition carry_lift7(t:term):term:=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma carry_lift7_eval M rho a b c d e f g t:
 evalM M(g.:f.:e.:d.:c.:b.:a.:rho)(carry_lift7 t)=evalM M rho t.
Proof. unfold evalM,carry_lift7;now rewrite !eval_up. Qed.
Definition machine230_carry_result M count left first last:=
 exists h r left' h' r' time slack,
 machine230_is_bit M h /\first=addM M(mulM M(code_numeral M 2)r)h /\
 machine230_is_bit M h' /\last=addM M(mulM M(code_numeral M 2)r')h' /\
 time=addM M count slack /\machine230_reaches_in M time
 (machine230_mk_config(carrier M)(zeroM M)left h r)
 (machine230_mk_config(carrier M)(zeroM M)left' h' r').
Definition carry_bit_formula(t:term):form:=t==zero ∨t==num 1.
Lemma carry_bit_formula_correct M rho t:holds M rho(carry_bit_formula t)<->machine230_is_bit M(evalM M rho t).
Proof. unfold carry_bit_formula,machine230_is_bit;rewrite holds_or;reflexivity. Qed.
Definition machine230_carry_result_formula(count left first last:term):form:=∃∃∃∃∃∃∃
 (carry_bit_formula $6 ∧(carry_lift7 first==num 2⊗$5⊕$6 ∧
 (carry_bit_formula $3 ∧(carry_lift7 last==num 2⊗$2⊕$3 ∧
 ($1==carry_lift7 count⊕$0 ∧machine230_reaches_in_formula $1 zero(carry_lift7 left)$6 $5 zero $4 $3 $2))))).
Definition machine230_carry_at M vb vc wb wc count:=
 machine230_carry_chain M vb vc wb wc count ->forall left first last,
 beta M wb wc(zeroM M)first ->beta M wb wc count last ->
 machine230_carry_result M count left first last.
Definition machine230_carry_at_formula:form:=
 machine230_carry_chain_formula $1 $2 $3 $4 $0 →∀∀∀
 (beta_formula $6 $7 zero $1 →beta_formula $6 $7 $3 $0 →
 machine230_carry_result_formula $3 $2 $1 $0).
Local Opaque Peano.sless holds beta_formula machine230_unary_block_formula machine230_reaches_in_formula.
Lemma machine230_carry_chain_formula_correct M rho vb vc wb wc count:
 holds M rho(machine230_carry_chain_formula vb vc wb wc count)<->
 machine230_carry_chain M(evalM M rho vb)(evalM M rho vc)(evalM M rho wb)(evalM M rho wc)(evalM M rho count).
Proof.
 unfold machine230_carry_chain_formula,machine230_carry_chain.
 rewrite holds_all. setoid_rewrite holds_imp. repeat setoid_rewrite holds_ex.
 repeat setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
 setoid_rewrite machine230_unary_block_formula_correct. setoid_rewrite less_formula_correct.
 repeat setoid_rewrite code_eval_lift4. setoid_rewrite register_eval_up. reflexivity.
Qed.
Lemma machine230_carry_result_formula_correct M rho count left first last:
 holds M rho(machine230_carry_result_formula count left first last)<->
 machine230_carry_result M(evalM M rho count)(evalM M rho left)(evalM M rho first)(evalM M rho last).
Proof.
 unfold machine230_carry_result_formula,machine230_carry_result.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite carry_bit_formula_correct. setoid_rewrite power_holds_equal.
 setoid_rewrite machine230_reaches_in_formula_correct.
 repeat setoid_rewrite register_eval_add. repeat setoid_rewrite register_eval_mul.
 repeat setoid_rewrite code_eval_num. repeat setoid_rewrite carry_lift7_eval. reflexivity.
Qed.
Theorem machine230_carry_at_definable M vb vc wb wc:
 Definable1 M(machine230_carry_at M vb vc wb wc).
Proof.
 exists machine230_carry_at_formula,(vb.:vc.:wb.:wc.:(fun _=>zeroM M)). intro count.
 unfold machine230_carry_at_formula,machine230_carry_at.
 rewrite holds_imp,machine230_carry_chain_formula_correct.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite beta_formula_correct. setoid_rewrite machine230_carry_result_formula_correct. reflexivity.
Qed.
Print Assumptions machine230_carry_chain_formula_correct.
Print Assumptions machine230_carry_result_formula_correct.
Print Assumptions machine230_carry_at_definable.
