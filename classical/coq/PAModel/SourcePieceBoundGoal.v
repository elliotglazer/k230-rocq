(** Literal existential PCf-bound conclusion: one ordinal strictly above
    g closes every piece of an internally finite table over X. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
  SourceRelativizationBounds SourceOrdinalPredicate SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionFormula
  SourcePieceConjunctionBounds SourcePieceLawFormulas.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_ordinal_predicate_code.

Definition source_pcf_bound_goal M domain level sb sc n g X out:=exists pc member left body,
  source_piece_conjunction M domain level sb sc n(zeroM M)(succM M X)pc /\
  sf_relation M SFMember(succM M g)(zeroM M)member /\
  sf_relation M SFAnd(source_ordinal_predicate_code M)member left /\sf_relation M SFAnd left pc body /\
  sf_relation M SFEx body(zeroM M)out.
Definition source_pcf_bound_goal_formula(domain level sb sc n g X out:term):form:=∃∃∃∃(
  source_piece_conjunction_formula(pc_lift4 domain)(pc_lift4 level)(pc_lift4 sb)(pc_lift4 sc)(pc_lift4 n)
    zero(σ(pc_lift4 X))$3 ∧(sf_formula SFMember(σ(pc_lift4 g))zero $2 ∧
    (sf_formula SFAnd(num(sf_encode source_ordinal_predicate))$2 $1 ∧
    (sf_formula SFAnd $1 $3 $0 ∧sf_formula SFEx $0 zero(pc_lift4 out))))).
Local Opaque holds source_piece_conjunction_formula sf_formula.

Theorem source_pcf_bound_goal_formula_correct M rho domain level sb sc n g X out:
  holds M rho(source_pcf_bound_goal_formula domain level sb sc n g X out) <->
  source_pcf_bound_goal M(evalM M rho domain)(evalM M rho level)(evalM M rho sb)(evalM M rho sc)
    (evalM M rho n)(evalM M rho g)(evalM M rho X)(evalM M rho out).
Proof.
  unfold source_pcf_bound_goal_formula,source_pcf_bound_goal.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_piece_conjunction_formula_correct. setoid_rewrite sf_formula_correct.
  repeat setoid_rewrite code_eval_num. setoid_rewrite SourcePieceLawFormulas.piece_eval_successor.
  setoid_rewrite pc_eval_lift4. reflexivity.
Qed.

Theorem source_pcf_bound_goal_total M domain level sb sc n g X:
  exists out,source_pcf_bound_goal M domain level sb sc n g X out.
Proof.
  destruct(source_piece_conjunction_total M domain level sb sc n(zeroM M)(succM M X)) as(pc&HPC).
  destruct(sf_relation_total M SFMember(succM M g)(zeroM M)) as(member&HM).
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)member) as(left&HL).
  destruct(sf_relation_total M SFAnd left pc) as(body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(out&HO).
  exists out,pc,member,left,body. auto.
Qed.

Theorem source_pcf_bound_goal_functional M domain level sb sc n g X a b:
  source_pcf_bound_goal M domain level sb sc n g X a ->source_pcf_bound_goal M domain level sb sc n g X b ->a=b.
Proof.
  intros(pa&ma&la&ba&HPA&HMA&HLA&HBA&HAA)(pb&mb&lb&bb&HPB&HMB&HLB&HBB&HAB).
  pose proof(source_piece_conjunction_functional M domain level sb sc n(zeroM M)(succM M X)pa pb HPA HPB) as E. subst pb.
  pose proof(sf_relation_functional M SFMember(succM M g)(zeroM M)ma mb HMA HMB) as E. subst mb.
  pose proof(sf_relation_functional M SFAnd(source_ordinal_predicate_code M)ma la lb HLA HLB) as E. subst lb.
  pose proof(sf_relation_functional M SFAnd la pa ba bb HBA HBB) as E. subst bb.
  exact(sf_relation_functional M SFEx ba(zeroM M)a b HAA HAB).
Qed.

Theorem source_pcf_bound_goal_bounded M domain level sb sc n g X out k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M g k ->coding_lt M X k ->
  source_pcf_bound_goal M domain level sb sc n g X out ->source_bounded M out k.
Proof.
  intros HD HL HV HG HX(pc&member&left&body&HPC&HM&HLeft&HBody&HEx).
  apply(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HEx)).
  apply(proj2(source_bounded_accept_binary M SFAnd left pc body(succM M k)(or_introl eq_refl)HBody)). split.
  - apply(proj2(source_bounded_accept_binary M SFAnd(source_ordinal_predicate_code M)member left(succM M k)
      (or_introl eq_refl)HLeft)). split.
    + exact(sr_domain_bound_succ M(source_ordinal_predicate_code M)k(source_ordinal_predicate_bounded M)).
    + exact(proj2(source_bounded_accept_atom M SFMember(succM M g)(zeroM M)member(succM M k)
        (or_introl eq_refl)HM)(conj(proj2(coding_lt_succ_cancel M g k)HG)(coding_zero_lt_succ M k))).
  - exact(source_piece_conjunction_bounded M n domain level sb sc(zeroM M)(succM M X)pc(succM M k)
      HD HL HV(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M X k)HX)HPC).
Qed.

Print Assumptions source_pcf_bound_goal_formula_correct.
Print Assumptions source_pcf_bound_goal_total.
Print Assumptions source_pcf_bound_goal_functional.
Print Assumptions source_pcf_bound_goal_bounded.
