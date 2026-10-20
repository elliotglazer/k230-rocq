(** Deterministic PA arithmetic allocation for the representative name.
    No choice over a predicate is used: W is an explicit polynomial term
    in the current allocation base, marker code and selected quotation. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalQuotation NumericalEnvironments QuotationHygiene QuotationFormulaFresh
  QuotationBinderFresh NamedBinderFresh FreshNames TemplateFormulaFresh
  RawQuotientAtomCongruence SupportedQuotientEnvironments.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Definition separation_base M a := succM M (succM M (succM M a)).
Definition separation_witness_name M a marker theta :=
  succM M (addM M (separation_base M a) (addM M marker theta)).

Lemma separation_lt_neq M x y : coding_lt M x y -> x<>y.
Proof. exact (@Peano.lt_neq (carrier M) (raw_interpretation M) (fun ax H rho=>axioms M ax rho H) x y). Qed.

Section AllocationBounds.
Variable M : Model.
Add Ring separation_ring : (model_semiring M).

Theorem separation_witness_bounds a marker theta :
  coding_lt M (separation_base M a) (separation_witness_name M a marker theta) /\
  coding_lt M marker (separation_witness_name M a marker theta) /\
  coding_lt M theta (separation_witness_name M a marker theta).
Proof.
  unfold separation_witness_name. split.
  - exists (addM M marker theta). reflexivity.
  - split.
    + exists (addM M (separation_base M a) theta). f_equal. ring.
    + exists (addM M (separation_base M a) marker). f_equal. ring.
Qed.
End AllocationBounds.

Theorem separation_named_bounds M a :
  coding_lt M (code_numeral M 1) a ->
  coding_lt M (zeroM M) a /\
  coding_lt M a (succM M a) /\
  coding_lt M (succM M a) (succM M (succM M a)) /\
  coding_lt M (succM M (succM M a)) (separation_base M a) /\
  coding_lt M (code_numeral M 2) (succM M a).
Proof.
  intro HT. split.
  - exact (coding_lt_trans M (zeroM M) (code_numeral M 1) a (coding_lt_succ M _) HT).
  - repeat split;try apply coding_lt_succ.
    exact (proj2 (coding_lt_succ_cancel M (code_numeral M 1) a) HT).
Qed.

Lemma separation_safe_above M b c n k l t :
  quotation_safe M b c n k t -> coding_lt M k l -> quotation_safe M b c n l t.
Proof.
  intros [HT HE] HK. split;[exact (coding_lt_trans M t k l HT HK)|].
  intros i v HV. exact (coding_lt_trans M v k l (HE i v HV) HK).
Qed.

Lemma separation_quote_fresh_at M phi eb ec en w wb wc wn t base f y :
  environment_cons M eb ec en w wb wc wn ->
  numerical_quotation M phi wb wc wn base t f ->
  environment_below M eb ec en y -> coding_lt M y w -> coding_lt M y base ->
  coding_lt M (zeroM M) y -> coding_lt M t y -> formula_fresh M f y.
Proof.
  intros HC HQ HE HY HW HZero HT.
  apply (numerical_quotation_formula_fresh M phi wb wc wn base t f y HQ HW).
  - intro E. subst y. exact (coding_not_lt_zero M (zeroM M) HZero).
  - exact (fun E=>separation_lt_neq M t y HT (Logic.eq_sym E)).
  - apply (quotation_environment_avoids_cons M eb ec en w wb wc wn y);[| |exact HC].
    + intros i v HV. exact (separation_lt_neq M v y (HE i v HV)).
    + exact (fun E=>separation_lt_neq M y w HY (Logic.eq_sym E)).
Qed.

Theorem raw_marker_above_fresh M t name marker y :
  raw_empty_marker_graph M t name marker -> coding_lt M name y -> formula_fresh M marker y.
Proof.
  intros [HN [HT HM]] HNY.
  set (env:=t .: name .: fun _=>zeroM M).
  assert (HName : expression_name_avoids M env y (CEvar 1)).
  { intros v HV. change (v=name) in HV. subst v. exact (separation_lt_neq M name y HNY). }
  assert (HTag : expression_name_avoids M env y (CEvar 0)).
  { intros v HV. change (v=t) in HV. subst v.
    exact (separation_lt_neq M t y (coding_lt_trans M t name y HT HNY)). }
  assert (HZero : y<>zeroM M).
  { intro E. subst y. exact (coding_not_lt_zero M name HNY). }
  apply (expression_fresh_universal M env y (CEvar 1) (E_wn (E_wel (CEvar 1) (CEvar 0))) HName).
  - apply expression_fresh_negation;[exact HZero|].
    apply expression_fresh_atom;[now left|exact HName|exact HTag].
  - exact HM.
Qed.

Theorem separation_witness_quotes M phi eb ec en a marker theta :
  quotation_safe M eb ec en a (code_numeral M 1) ->
  exists wb wc wn f,
    environment_cons M eb ec en (separation_witness_name M a marker theta) wb wc wn /\
    quotation_safe M wb wc wn (succM M (separation_witness_name M a marker theta)) (code_numeral M 1) /\
    numerical_quotation M phi wb wc wn (succM M (separation_witness_name M a marker theta)) (code_numeral M 1) f /\
    formula_fresh M marker (separation_witness_name M a marker theta) /\
    formula_fresh M theta (separation_witness_name M a marker theta) /\
    named_binder_absent M f (separation_witness_name M a marker theta).
Proof.
  intro HS. destruct (separation_witness_bounds M a marker theta) as [HB [HM HQ]].
  assert (HA : coding_lt M a (separation_witness_name M a marker theta)).
  { apply (coding_lt_trans M a (separation_base M a));[|exact HB].
    apply (coding_lt_trans M a (succM M a));[apply coding_lt_succ|].
    apply (coding_lt_trans M (succM M a) (succM M (succM M a)));apply coding_lt_succ. }
  destruct (environment_cons_total M eb ec en (separation_witness_name M a marker theta)) as [wb [wc [wn HC]]].
  pose proof (quotation_safe_cons M eb ec en (separation_witness_name M a marker theta)
    (code_numeral M 1) wb wc wn (separation_safe_above M eb ec en a _ _ HS HA) HC) as HSafe.
  destruct (numerical_quotation_total M phi wb wc wn (succM M (separation_witness_name M a marker theta))
    (code_numeral M 1)) as [f HF].
  exists wb,wc,wn,f. split;[exact HC|]. split;[exact HSafe|]. split;[exact HF|].
  split;[exact (formula_above_is_fresh M marker _ HM)|].
  split;[exact (formula_above_is_fresh M theta _ HQ)|].
  exact (numerical_quotation_binder_fresh M phi wb wc wn (succM M (separation_witness_name M a marker theta))
    (code_numeral M 1) f (separation_witness_name M a marker theta) HF (coding_lt_succ M _)).
Qed.

Print Assumptions separation_witness_bounds.
Print Assumptions separation_witness_quotes.
Print Assumptions raw_marker_above_fresh.
