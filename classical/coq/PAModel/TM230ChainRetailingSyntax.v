(** Arithmetic syntax for rebuilding an internal register suffix at any tail. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions
 NumericalProofs TM230UnaryBlocks TM230RegisterWords TM230CarryChainSyntax.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition machine230_carry_chain_from M vb vc start wb wc count:=forall i,coding_lt M i count ->
 exists v word next,beta M vb vc(addM M start i)v /\beta M wb wc i word /\
 beta M wb wc(succM M i)next /\machine230_unary_block M v next word.
Definition machine230_carry_chain_from_formula(vb vc start wb wc count:term):form:=∀
 (Peano.sless $0 count`[↑]→∃∃∃
 (beta_formula(code_lift4 vb)(code_lift4 vc)(code_lift4 start⊕$3)$2 ∧
 (beta_formula(code_lift4 wb)(code_lift4 wc)$3 $1 ∧
 (beta_formula(code_lift4 wb)(code_lift4 wc)(σ $3)$0 ∧
 machine230_unary_block_formula $2 $0 $1)))).
Definition machine230_carry_chain_retail_at M vb vc count:=forall start tail,
 exists wb wc first,beta M wb wc(zeroM M)first /\beta M wb wc count tail /\
 machine230_carry_chain_from M vb vc start wb wc count.
Definition machine230_carry_chain_retail_formula:form:=∀∀∃∃∃
 (beta_formula $2 $1 zero $0 ∧(beta_formula $2 $1 $5 $3 ∧
 machine230_carry_chain_from_formula $6 $7 $4 $2 $1 $5)).
Local Opaque holds Peano.sless beta_formula machine230_unary_block_formula.
Lemma machine230_carry_chain_from_formula_correct M rho vb vc start wb wc count:
 holds M rho(machine230_carry_chain_from_formula vb vc start wb wc count)<->
 machine230_carry_chain_from M(evalM M rho vb)(evalM M rho vc)(evalM M rho start)
 (evalM M rho wb)(evalM M rho wc)(evalM M rho count).
Proof.
 unfold machine230_carry_chain_from_formula,machine230_carry_chain_from.
 rewrite holds_all. setoid_rewrite holds_imp. repeat setoid_rewrite holds_ex.
 repeat setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
 setoid_rewrite machine230_unary_block_formula_correct. setoid_rewrite less_formula_correct.
 repeat setoid_rewrite register_eval_add. repeat setoid_rewrite code_eval_lift4.
 setoid_rewrite register_eval_up. reflexivity.
Qed.
Local Opaque machine230_carry_chain_from_formula.
Theorem machine230_carry_chain_retail_definable M vb vc:
 Definable1 M(machine230_carry_chain_retail_at M vb vc).
Proof.
 exists machine230_carry_chain_retail_formula,(vb.:vc.:(fun _=>zeroM M)). intro count.
 unfold machine230_carry_chain_retail_formula,machine230_carry_chain_retail_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite beta_formula_correct. setoid_rewrite machine230_carry_chain_from_formula_correct. reflexivity.
Qed.
Print Assumptions machine230_carry_chain_from_formula_correct.
Print Assumptions machine230_carry_chain_retail_definable.
