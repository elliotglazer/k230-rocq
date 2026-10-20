(** A unary carrier predicate expressing witness closure of one pcs piece
    for all its internally many parameters. This is syntax, not an assumed
    proof of witness closure. It is the first-order input for uniform TV. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceEwMonotone SourceEwAtSyntax
  SourceBallS SourceBallSBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.
Definition source_piece_witness_unary M domain count piece out:=exists ew,
  source_ew_at M domain piece count ew /\source_ballS M count(zeroM M)ew out.
Definition source_piece_witness_unary_formula(domain count piece out:term):form:=∃(
  source_ew_at_formula domain`[↑] piece`[↑] count`[↑] $0 ∧source_ballS_formula count`[↑] zero $0 out`[↑]).
Local Opaque holds source_ew_at_formula source_ballS_formula.
Theorem source_piece_witness_unary_formula_correct M rho domain count piece out:
  holds M rho(source_piece_witness_unary_formula domain count piece out) <->
  source_piece_witness_unary M(evalM M rho domain)(evalM M rho count)(evalM M rho piece)(evalM M rho out).
Proof.
  unfold source_piece_witness_unary_formula,source_piece_witness_unary.
  setoid_rewrite holds_ex. setoid_rewrite holds_and. setoid_rewrite source_ew_at_formula_correct.
  setoid_rewrite source_ballS_formula_correct. unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_piece_witness_unary_total M domain count piece:
  exists out,source_piece_witness_unary M domain count piece out.
Proof.
  destruct(source_ew_at_total M domain piece count)as(ew&HE).
  destruct(source_ballS_total M count(zeroM M)ew)as(out&HO). exists out,ew. auto.
Qed.
Theorem source_piece_witness_unary_functional M domain count piece x y:
  source_piece_witness_unary M domain count piece x ->source_piece_witness_unary M domain count piece y ->x=y.
Proof.
  intros(ew&HE&HX)(ew'&HE'&HY).
  pose proof(source_ew_at_functional M domain piece count ew' ew HE' HE)as E. subst ew'.
  exact(source_ballS_functional M count(zeroM M)ew x y HX HY).
Qed.
Theorem source_piece_witness_unary_bounded M domain count piece out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  source_piece_witness_unary M domain count piece out ->source_bounded M out(code_numeral M 1).
Proof.
  intros HD HP(ew&HE&HO).
  assert(HP':source_bounded M piece(succM M(succM M count))).
  { apply(source_bounded_monotone M piece(succM M count)(succM M(succM M count))HP).
    exact(coding_lt_trans M(succM M count)(succM M(succM M count))(succM M(succM M(succM M count)))
      (coding_lt_succ M(succM M count))(coding_lt_succ M(succM M(succM M count)))). }
  pose proof(source_ew_at_bounded M domain piece count ew(succM M count)HD HP'(coding_lt_succ M count)HE)as BE.
  apply(source_ballS_bounded M count(zeroM M)ew out(code_numeral M 1)HO(coding_lt_succ M(zeroM M))).
  change(source_bounded M ew(addM M count(succM M(zeroM M)))).
  now rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Print Assumptions source_piece_witness_unary_formula_correct.
Print Assumptions source_piece_witness_unary_total.
Print Assumptions source_piece_witness_unary_functional.
Print Assumptions source_piece_witness_unary_bounded.
