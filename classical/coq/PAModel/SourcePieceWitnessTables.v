(** Pack literal witness-closure formulas for an internally finite piece
    table. Both the number of pieces and each parameter count may be nonstandard. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  Pairing NumericalContexts SourcePieceWitnessInstance BoundedCollection.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.

Definition source_piece_witness_table M domain Y sb sc count wb wc:=
  forall i entry pc piece out,coding_lt M i count ->beta M sb sc i entry ->
    pair_graph M pc piece entry ->beta M wb wc i out ->
    source_piece_witness_instance M domain pc piece Y out.

Definition source_piece_witness_table_step_formula:form:=∃∃∃(
  beta_formula $5 $6 $4 $2 ∧pair_formula $1 $0 $2 ∧
  source_piece_witness_instance_formula $7 $1 $0 $8 $3).
Local Opaque holds beta_formula pair_formula source_piece_witness_instance_formula.

Theorem source_piece_witness_table_step_correct M domain Y sb sc i out:
  holds M(out .: i .: sb .: sc .: domain .: Y .: fun _=>zeroM M)
    source_piece_witness_table_step_formula <->
  exists entry pc piece,beta M sb sc i entry /\pair_graph M pc piece entry /\
    source_piece_witness_instance M domain pc piece Y out.
Proof.
  unfold source_piece_witness_table_step_formula.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite pair_formula_correct.
  setoid_rewrite source_piece_witness_instance_formula_correct.
  split;intros(entry&pc&piece&H);exists entry,pc,piece;tauto.
Qed.

Theorem source_piece_witness_table_total M domain Y sb sc count:
  exists wb wc,source_piece_witness_table M domain Y sb sc count wb wc.
Proof.
  assert(HTotal:collection_total M source_piece_witness_table_step_formula
    (sb .: sc .: domain .: Y .: fun _=>zeroM M)count).
  { intros i _. destruct(beta_total M sb sc i)as(entry&HE).
    destruct(pair_surjective M entry)as(pc&piece&HP).
    destruct(source_piece_witness_instance_total M domain pc piece Y)as(out&HO).
    exists out. apply(proj2(source_piece_witness_table_step_correct M domain Y sb sc i out)).
    exists entry,pc,piece. auto. }
  destruct(bounded_collection_table M source_piece_witness_table_step_formula
    (sb .: sc .: domain .: Y .: fun _=>zeroM M)count HTotal)as(wb&wc&HT).
  exists wb,wc. intros i entry pc piece out HI HE HP HO.
  pose proof(proj1(source_piece_witness_table_step_correct M domain Y sb sc i out)
    (HT i out HI HO))as HResult.
  destruct HResult as(entry'&pc'&piece'&HE'&HP'&HOut).
  pose proof(beta_unique M sb sc i entry entry' HE HE')as E. subst entry'.
  destruct(pair_injective M entry pc piece pc' piece' HP HP')as(Epc&Epiece).
  now subst pc' piece'.
Qed.

Theorem source_piece_witness_table_entries M domain Y sb sc count wb wc:
  source_piece_witness_table M domain Y sb sc count wb wc ->forall out,
  context_member M wb wc count out <->exists entry pc piece,
    context_member M sb sc count entry /\pair_graph M pc piece entry /\
    source_piece_witness_instance M domain pc piece Y out.
Proof.
  intros HT out. split.
  - intros(i&HI&HO). destruct(beta_total M sb sc i)as(entry&HE).
    destruct(pair_surjective M entry)as(pc&piece&HP).
    exists entry,pc,piece. split;[exists i;auto|]. split;[exact HP|].
    exact(HT i entry pc piece out HI HE HP HO).
  - intros(entry&pc&piece&(i&HI&HE)&HP&HOut).
    destruct(beta_total M wb wc i)as(out'&HO).
    pose proof(HT i entry pc piece out' HI HE HP HO)as HOut'.
    pose proof(source_piece_witness_instance_functional M domain pc piece Y out out' HOut HOut')as E.
    subst out'. exists i. auto.
Qed.

Print Assumptions source_piece_witness_table_step_correct.
Print Assumptions source_piece_witness_table_total.
Print Assumptions source_piece_witness_table_entries.
