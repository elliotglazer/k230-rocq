(** Arithmetic recognition of the exact raw subset and four-implication
    source laws used in internally finite piece proof induction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceRawSubset SourceThreeConditions.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_piece_subset_formula(x y out:term):form:=∃∃∃(
  sf_formula SFMember zero(σ(lift3 x))$2 ∧(sf_formula SFMember zero(σ(lift3 y))$1 ∧
    (sf_formula SFImpl $2 $1 $0 ∧sf_formula SFAll $0 zero(lift3 out)))).
Definition source_piece_curried_formula(a b c d e out:term):form:=∃∃∃(
  sf_formula SFImpl(lift3 d)(lift3 e)$2 ∧(sf_formula SFImpl(lift3 c)$2 $1 ∧
    (sf_formula SFImpl(lift3 b)$1 $0 ∧sf_formula SFImpl(lift3 a)$0(lift3 out)))).
Local Opaque holds sf_formula.
Lemma piece_eval_successor M rho t:evalM M rho(σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.

Theorem source_piece_subset_formula_correct M rho x y out:
  holds M rho(source_piece_subset_formula x y out) <->
  source_raw_subset_graph M(evalM M rho x)(evalM M rho y)(evalM M rho out).
Proof.
  unfold source_piece_subset_formula,source_raw_subset_graph.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and. setoid_rewrite sf_formula_correct.
  setoid_rewrite piece_eval_successor.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_piece_curried_formula_correct M rho a b c d e out:
  holds M rho(source_piece_curried_formula a b c d e out) <->
  source_three_curried M(evalM M rho a)(evalM M rho b)(evalM M rho c)(evalM M rho d)(evalM M rho e)(evalM M rho out).
Proof.
  unfold source_piece_curried_formula,source_three_curried.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and. setoid_rewrite sf_formula_correct.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Print Assumptions source_piece_subset_formula_correct.
Print Assumptions source_piece_curried_formula_correct.
