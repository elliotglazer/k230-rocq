(** One free-variable bound for every formula and context in an internally
    finite source proof trace. Rule parameters used only in existential
    witnesses, such as an unused instantiation term, are not bounded here. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs NumericalTraces NumericalContexts SourceSequents
  SourceBounded SourceBoundMonotone NumericalSourceFull SourceQuantifierRules
  BoundedCollection.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_row_at_bound M r k :=
  (exists b c n f, source_sequent M b c n f r /\ source_bounded M f k /\ context_bounded M b c n k) \/
  (exists b c n a d f, source_branches M b c n a d f r /\
    source_bounded M a k /\ source_bounded M d k /\ source_bounded M f k /\ context_bounded M b c n k).

Definition trace_bounds_lift6 (t : term) : term := t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma trace_bounds_lift6_correct M rho a b c d e f t :
  evalM M (a .: b .: c .: d .: e .: f .: rho) (trace_bounds_lift6 t) = evalM M rho t.
Proof. unfold trace_bounds_lift6,evalM. now rewrite !eval_up. Qed.

Definition source_row_at_bound_formula (r k : term) : form :=
  (∃∃∃∃ (source_sequent_formula $3 $2 $1 $0 (lift4 r) ∧
    (source_bounded_accept_formula $0 (lift4 k) ∧ context_bounded_formula $3 $2 $1 (lift4 k)))) ∨
  (∃∃∃∃∃∃ (source_branches_formula $5 $4 $3 $2 $1 $0 (trace_bounds_lift6 r) ∧
    (source_bounded_accept_formula $2 (trace_bounds_lift6 k) ∧
    (source_bounded_accept_formula $1 (trace_bounds_lift6 k) ∧
    (source_bounded_accept_formula $0 (trace_bounds_lift6 k) ∧
      context_bounded_formula $5 $4 $3 (trace_bounds_lift6 k)))))).

Local Opaque holds source_sequent_formula source_branches_formula
  source_bounded_accept_formula context_bounded_formula.
Lemma source_row_at_bound_formula_correct M rho r k :
  holds M rho (source_row_at_bound_formula r k) <->
  source_row_at_bound M (evalM M rho r) (evalM M rho k).
Proof.
  unfold source_row_at_bound_formula,source_row_at_bound.
  setoid_rewrite holds_or. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite source_branches_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite lift4_correct. setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Lemma source_row_wf_has_bound M r : source_row_wf M r -> exists k, source_row_at_bound M r k.
Proof.
  intros [[b [c [n [f [Hr [k [Hf HC]]]]]]]|[b [c [n [a [d [f [Hr [k [Ha [Hd [Hf HC]]]]]]]]]]]].
  - exists k. left. exists b,c,n,f. auto.
  - exists k. right. exists b,c,n,a,d,f. auto.
Qed.

Lemma context_bounded_monotone M b c n k l :
  context_bounded M b c n k -> coding_lt M k (succM M l) -> context_bounded M b c n l.
Proof. intros H Hkl f Hf. exact (source_bounded_monotone M f k l (H f Hf) Hkl). Qed.

Lemma source_row_at_bound_monotone M r k l :
  source_row_at_bound M r k -> coding_lt M k (succM M l) -> source_row_at_bound M r l.
Proof.
  intros [[b [c [n [f [Hr [Hf HC]]]]]]|[b [c [n [a [d [f [Hr [Ha [Hd [Hf HC]]]]]]]]]]] Hkl.
  - left. exists b,c,n,f. split; [exact Hr|]. split.
    + exact (source_bounded_monotone M f k l Hf Hkl).
    + exact (context_bounded_monotone M b c n k l HC Hkl).
  - right. exists b,c,n,a,d,f. split; [exact Hr|]. repeat split.
    + exact (source_bounded_monotone M a k l Ha Hkl).
    + exact (source_bounded_monotone M d k l Hd Hkl).
    + exact (source_bounded_monotone M f k l Hf Hkl).
    + exact (context_bounded_monotone M b c n k l HC Hkl).
Qed.

Lemma source_trace_row_wf M b c n i r :
  trace_sequence M source_full_rules b c n -> coding_lt M i n -> beta M b c i r -> source_row_wf M r.
Proof.
  intros HS Hi Hr. apply source_full_row_wellformed. exists b,c,i. split; [|exact Hr].
  intros j v Hj Hv. apply (HS j v); [|exact Hv].
  destruct (proj1 (coding_lt_succ_cases M j i) Hj) as [Hji|E].
  - exact (coding_lt_trans M j i n Hji Hi).
  - now subst j.
Qed.

Definition source_trace_bound_witness_formula : form :=
  ∃ (beta_formula $3 $4 $2 $0 ∧ source_row_at_bound_formula $0 $1).
Local Opaque beta_formula source_row_at_bound_formula.
Lemma source_trace_bound_witness_correct M b c i k :
  holds M (k .: i .: b .: c .: fun _ => zeroM M) source_trace_bound_witness_formula <->
  exists r, beta M b c i r /\ source_row_at_bound M r k.
Proof.
  unfold source_trace_bound_witness_formula.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite source_row_at_bound_formula_correct. reflexivity.
Qed.

Theorem source_trace_common_bound M b c n :
  trace_sequence M source_full_rules b c n ->
  exists bound, forall i r, coding_lt M i n -> beta M b c i r -> source_row_at_bound M r bound.
Proof.
  intro HS.
  assert (HT : forall i, coding_lt M i n -> exists k,
    holds M (k .: i .: b .: c .: fun _ => zeroM M) source_trace_bound_witness_formula).
  { intros i Hi. destruct (beta_total M b c i) as [r Hr].
    destruct (source_row_wf_has_bound M r (source_trace_row_wf M b c n i r HS Hi Hr)) as [k Hk].
    exists k. apply source_trace_bound_witness_correct. exists r. auto. }
  destruct (bounded_collection M source_trace_bound_witness_formula
    (b .: c .: fun _ => zeroM M) n HT) as [bound HB].
  exists bound. intros i r Hi Hr. destruct (HB i Hi) as [k [Hkb Hk]].
  apply source_trace_bound_witness_correct in Hk as [r' [Hr' Hk]].
  assert (r'=r) by (exact (beta_unique M b c i r' r Hr' Hr)). subst r'.
  apply (source_row_at_bound_monotone M r k bound Hk).
  apply (proj2 (coding_lt_succ_cases M k bound)). now left.
Qed.

Print Assumptions source_row_at_bound_formula_correct.
Print Assumptions source_trace_common_bound.
