(** Exact target of the varying-matrix least-ordinal argument. The input
    predicate has witness variable0 and arbitrary remaining parameters. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceRelativizationBounds
  SchemaConstructorBounds SourceOrdinalPredicate SourceFiniteCutoffShift.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition least_ordinal_expression := E_sf_ex
  (E_sf SFAnd
    (E_sf SFAnd (CEconst (sf_encode source_ordinal_predicate)) (CEvar 0))
    (E_sf_all (E_sf SFImpl (E_sf_mem 0 1) (E_sf SFImpl (CEvar 1) (CEconst 0))))).
Definition source_least_ordinal_graph M phi least := exists inserted,
  source_cutoff_shift M 1 phi inserted /\
  code_relation M (sf_env phi inserted) least_ordinal_expression least.
Definition source_least_ordinal_formula (phi least:term) : form :=
  ∃ (source_cutoff_shift_formula 1 (phi`[↑]) $0 ∧
    code_formula least_ordinal_expression (sf_env (phi`[↑]) $0) (least`[↑])).
Local Opaque holds source_cutoff_shift_formula.

Theorem source_least_ordinal_formula_correct M rho phi least :
  holds M rho (source_least_ordinal_formula phi least) <->
  source_least_ordinal_graph M (evalM M rho phi) (evalM M rho least).
Proof.
  unfold source_least_ordinal_formula,source_least_ordinal_graph.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_cutoff_shift_formula_correct. setoid_rewrite code_formula_correct.
  unfold evalM. setoid_rewrite eval_up.
  assert (EE:forall x i,evalM M (x .: rho) (sf_env (phi`[↑]) $0 i)=sf_env (evalM M rho phi) x i).
  { intros x [|i];cbn [sf_env];unfold evalM;try rewrite eval_up;reflexivity. }
  split;intros [x [HI HG]];exists x;split;[exact HI| |exact HI|].
  - exact (proj1 (code_relation_ext M least_ordinal_expression
      (fun index => evalM M (x .: rho) (sf_env (phi`[↑]) $0 index))
      (sf_env (evalM M rho phi) x) (evalM M rho least) (EE x)) HG).
  - exact (proj2 (code_relation_ext M least_ordinal_expression
      (fun index => evalM M (x .: rho) (sf_env (phi`[↑]) $0 index))
      (sf_env (evalM M rho phi) x) (evalM M rho least) (EE x)) HG).
Qed.

Theorem source_least_ordinal_total M phi :exists least,source_least_ordinal_graph M phi least.
Proof.
  destruct (source_cutoff_shift_total M 1 phi) as [inserted HI].
  destruct (code_relation_total M least_ordinal_expression (sf_env phi inserted)) as [least HG].
  exists least,inserted. auto.
Qed.

Theorem source_least_ordinal_bound M phi least count :
  source_bounded M phi (succM M count) ->source_least_ordinal_graph M phi least ->
  source_bounded M least count.
Proof.
  intros HP [inserted [HI HG]].
  pose proof (source_cutoff_shift_bounded M 1 phi inserted count HP HI) as HInserted.
  assert (HBound:schema_expression_bound M (sf_env phi inserted) least_ordinal_expression count).
  { unfold least_ordinal_expression,E_sf_ex,E_sf_all,E_sf_mem.
    repeat schema_constructor_bound;try schema_small_index.
    - exact (sr_domain_bound_succ M _ count (source_ordinal_predicate_bounded M)).
    - exact HP.
    - exact HInserted.
    - apply source_bounded_accept_falsity. }
  exact (HBound least HG).
Qed.

Print Assumptions source_least_ordinal_formula_correct.
Print Assumptions source_least_ordinal_total.
Print Assumptions source_least_ordinal_bound.
