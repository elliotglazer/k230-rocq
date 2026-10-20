(** One definable invariant retains the same arithmetic tables in both directions. *)
From PAModel Require Import Model FiniteCoding NumericalProofs TM230CarryChainSyntax
 TM230CarryPrefixes TM230ViewRuns.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
Definition machine230_carry_rollback_at M vb vc wb wc lb lc count:=forall a b x y,
 machine230_carry_chain M vb vc wb wc count ->
 machine230_carry_prefix_chain M vb vc lb lc count ->
 beta M lb lc(zeroM M)a ->beta M lb lc count b ->
 beta M wb wc(zeroM M)x ->beta M wb wc count y ->
 machine230_bounded_view_run M false 0 count a x b y /\
 machine230_bounded_view_run M true 97 count y b x a.
Definition machine230_carry_rollback_at_formula:form:=∀∀∀∀
 (machine230_carry_chain_formula $5 $6 $7 $8 $4 →
 machine230_carry_prefix_chain_formula $5 $6 $9 $10 $4 →
 beta_formula $9 $10 zero $3 →beta_formula $9 $10 $4 $2 →
 beta_formula $7 $8 zero $1 →beta_formula $7 $8 $4 $0 →
 (machine230_bounded_view_run_formula false 0 $4 $3 $1 $2 $0 ∧
 machine230_bounded_view_run_formula true 97 $4 $0 $2 $1 $3)).
Local Opaque holds machine230_carry_chain_formula machine230_carry_prefix_chain_formula beta_formula
 machine230_bounded_view_run_formula.
Theorem machine230_carry_rollback_definable M vb vc wb wc lb lc:
 Definable1 M(machine230_carry_rollback_at M vb vc wb wc lb lc).
Proof.
 exists machine230_carry_rollback_at_formula,(vb.:vc.:wb.:wc.:lb.:lc.:(fun _=>zeroM M)). intro n.
 unfold machine230_carry_rollback_at_formula,machine230_carry_rollback_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp. setoid_rewrite holds_and.
 setoid_rewrite machine230_carry_chain_formula_correct.
 setoid_rewrite machine230_carry_prefix_chain_formula_correct.
 setoid_rewrite beta_formula_correct. setoid_rewrite machine230_bounded_view_run_formula_correct. reflexivity.
Qed.
Print Assumptions machine230_carry_rollback_definable.
