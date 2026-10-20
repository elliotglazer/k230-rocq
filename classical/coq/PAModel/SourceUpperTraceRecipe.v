(** The exact trace_predicate matrix used in KUpperCore.  Its graph and
    bound preservation apply to arbitrary internal source matrix codes.
    This is syntax for a required Separation instance, not a claim that
    the uniform L-reflection or upper-core proof has been constructed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent SourceBounded NumericalRenaming SourceFiniteCutoffShift
  SourceFixedSwap SourceNumeralLift NumericalZFCAxioms NumericalCoreAxioms
  SetSchemaConstructors NumericalSetClosure.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures Sets.minZF.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_upper_trace M phi out :=exists swapped shifted atom body,
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) swapped /\
  source_cutoff_shift M 2 swapped shifted /\
  sf_relation M SFMember (zeroM M) (code_numeral M 2) atom /\
  sf_relation M SFAnd atom shifted body /\ sf_relation M SFEx body (zeroM M) out.
Definition source_upper_trace_formula (phi out:term) :form :=
  ∃∃∃∃ (numerical_renaming_formula (lift4 phi) (num 3) (num 1) (num 2) zero $3 ∧
    (source_cutoff_shift_formula 2 $3 $2 ∧
    (sf_formula SFMember zero (num 2) $1 ∧
    (sf_formula SFAnd $1 $2 $0 ∧ sf_formula SFEx $0 zero (lift4 out))))).
Local Opaque holds numerical_renaming_formula source_cutoff_shift_formula sf_formula.

Theorem source_upper_trace_formula_correct M rho phi out :
  holds M rho (source_upper_trace_formula phi out) <->
  source_upper_trace M (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_upper_trace_formula,source_upper_trace.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_cutoff_shift_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,lift4. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_upper_trace_total M phi :exists out,source_upper_trace M phi out.
Proof.
  destruct (numerical_renaming_total M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M)) as (swapped&HS).
  destruct (source_cutoff_shift_total M 2 swapped) as (shifted&HT).
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 2)) as (atom&HA).
  destruct (sf_relation_total M SFAnd atom shifted) as (body&HB).
  destruct (sf_relation_total M SFEx body (zeroM M)) as (out&HO).
  exists out,swapped,shifted,atom,body. auto.
Qed.

Theorem source_upper_trace_bounded M phi out n :
  source_bounded M phi (succM M (succM M n)) ->
  source_upper_trace M phi out ->source_bounded M out (succM M (succM M n)).
Proof.
  intros HP (swapped&shifted&atom&body&HS&HT&HA&HB&HO).
  pose proof (source_fixed_swap_bounded M phi swapped n HP HS) as HSwap.
  pose proof (source_cutoff_shift_bounded M 2 swapped shifted n HSwap HT) as HShift.
  apply (proj2 (source_bounded_accept_unary M SFEx body out (succM M (succM M n))
    (or_intror eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFAnd atom shifted body
    (succM M (succM M (succM M n))) (or_introl eq_refl) HB)). split;[|exact HShift].
  apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 2) atom
    (succM M (succM M (succM M n))) (or_introl eq_refl) HA)). split.
  - apply coding_zero_lt_succ.
  - apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Definition upper_trace_source (phi:sf_form) :sf_form :=
  ∃ ($0 ∈' $2 ∧ phi[$1 .: $0 .: (fun k=>var (3+k))]).

Lemma upper_trace_matrix_composition (phi:sf_form) :
  phi[source_swap_sigma][source_shift_sigma 2] =phi[$1 .: $0 .: (fun k=>var (3+k))].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|[|i]];reflexivity.
Qed.

Theorem source_upper_trace_finite_lift M (phi:sf_form) :
  source_upper_trace M (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode (upper_trace_source phi))).
Proof.
  set (swapped:=phi[source_swap_sigma]).
  set (shifted:=swapped[source_shift_sigma 2]).
  assert (E:shifted=phi[$1 .: $0 .: (fun k=>var (3+k))]) by apply upper_trace_matrix_composition.
  exists (code_numeral M (sf_encode swapped)),(code_numeral M (sf_encode shifted)),
    (code_numeral M (sf_make SFMember 0 2)),
    (code_numeral M (sf_make SFAnd (sf_make SFMember 0 2) (sf_encode shifted))).
  split;[exact (source_fixed_swap_finite_lift M phi)|]. split.
  - exact (source_cutoff_shift_fixed_source M 2 (fun _=>zeroM M) swapped _ _
      (source_formula_numeral_graph M swapped) (source_formula_numeral_graph M shifted)).
  - split;[exact (sf_make_numeral M SFMember 0 2)|]. split.
    + exact (sf_make_numeral M SFAnd (sf_make SFMember 0 2) (sf_encode shifted)).
    + unfold upper_trace_source. rewrite <-E.
      exact (sf_make_numeral M SFEx (sf_make SFAnd (sf_make SFMember 0 2) (sf_encode shifted)) 0).
Qed.

Print Assumptions source_upper_trace_formula_correct.
Print Assumptions source_upper_trace_total.
Print Assumptions source_upper_trace_bounded.
Print Assumptions source_upper_trace_finite_lift.
