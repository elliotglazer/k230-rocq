(** Arithmetic construction of a composed environment of exactly the required
    length. Uses bounded formula beta packing, not external function choice. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula BetaExtension BetaPacking NumericalProofs SentenceBounds
  NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution
  NumericalQuotation SourceBounded QuotationHygiene
  SubstitutionEnvironment QuotationSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_composed_lookup M sb sc sn base eb ec en i v :=
  exists x, substitution_lookup M sb sc sn base i x /\ environment_lookup M eb ec en x v.
Definition substitution_composed_lookup_formula
    (sb sc sn base eb ec en i v : term) : form :=
  ∃ (substitution_lookup_formula sb`[↑] sc`[↑] sn`[↑] base`[↑] i`[↑] $0 ∧
     environment_lookup_formula eb`[↑] ec`[↑] en`[↑] $0 v`[↑]).

Local Opaque holds substitution_lookup_formula environment_lookup_formula.
Lemma substitution_composed_lookup_formula_correct M rho sb sc sn base eb ec en i v :
  holds M rho (substitution_composed_lookup_formula sb sc sn base eb ec en i v) <->
  substitution_composed_lookup M (evalM M rho sb) (evalM M rho sc)
    (evalM M rho sn) (evalM M rho base) (evalM M rho eb) (evalM M rho ec)
    (evalM M rho en) (evalM M rho i) (evalM M rho v).
Proof.
  unfold substitution_composed_lookup_formula,substitution_composed_lookup.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite environment_lookup_formula_correct.
  unfold evalM. now repeat setoid_rewrite eval_up.
Qed.

Lemma substitution_composed_lookup_total M sb sc sn base eb ec en i :
  exists v, substitution_composed_lookup M sb sc sn base eb ec en i v.
Proof.
  destruct (substitution_lookup_total M sb sc sn base i) as [x Hx].
  destruct (environment_lookup_total M eb ec en x) as [v Hv].
  exists v,x. auto.
Qed.

Lemma environment_lookup_dividend_bound M b c n i v :
  environment_lookup M b c n i v -> coding_lt M v (succM M b).
Proof.
  intros [[Hi Hv]|[Hi Hv]].
  - exact (remainder_le_dividend M b (beta_modulus M c i) v Hv).
  - subst v. apply coding_zero_lt_succ.
Qed.

Lemma substitution_composed_lookup_bound M sb sc sn base eb ec en i v :
  substitution_composed_lookup M sb sc sn base eb ec en i v ->
  coding_lt M v (succM M eb).
Proof.
  intros [x [Hx Hv]]. exact (environment_lookup_dividend_bound M eb ec en x v Hv).
Qed.

Lemma substitution_composed_lookup_functional M sb sc sn base eb ec en i v w :
  substitution_composed_lookup M sb sc sn base eb ec en i v ->
  substitution_composed_lookup M sb sc sn base eb ec en i w -> v=w.
Proof.
  intros [x [Hx Hv]] [y [Hy Hw]].
  assert (x=y) by exact (substitution_lookup_functional M sb sc sn base i x y Hx Hy).
  subst y. exact (environment_lookup_functional M eb ec en x v w Hv Hw).
Qed.

Definition substitution_composition_entry_formula : form :=
  substitution_composed_lookup_formula $8 $7 $6 $5 $4 $3 $2 $1 $0.

Lemma substitution_composition_entry_correct M rho sb sc sn base eb ec en i v :
  holds M (v .: i .: en .: ec .: eb .: base .: sn .: sc .: sb .: rho)
    substitution_composition_entry_formula <->
  substitution_composed_lookup M sb sc sn base eb ec en i v.
Proof. apply substitution_composed_lookup_formula_correct. Qed.

(** The output environment has the exact length bound. Its encoding need not
    be unique, but every live entry is the intended composition. *)
Theorem substitution_composed_environment_total M sb sc sn base eb ec en bound :
  exists fb fc, forall i v, coding_lt M i bound ->
    (environment_lookup M fb fc bound i v <->
     substitution_composed_lookup M sb sc sn base eb ec en i v).
Proof.
  set (rho := en .: ec .: eb .: base .: sn .: sc .: sb .: fun _ => zeroM M).
  assert (Ht : forall i, coding_lt M i bound ->
    exists v, holds M (v .: i .: rho) substitution_composition_entry_formula).
  { intros i _. destruct (substitution_composed_lookup_total M sb sc sn base eb ec en i)
      as [v Hv]. exists v. unfold rho. apply substitution_composition_entry_correct. exact Hv. }
  assert (Hb : forall i v, coding_lt M i bound ->
    holds M (v .: i .: rho) substitution_composition_entry_formula -> coding_lt M v (succM M eb)).
  { intros i v _ Hv. unfold rho in Hv. apply substitution_composition_entry_correct in Hv.
    exact (substitution_composed_lookup_bound M sb sc sn base eb ec en i v Hv). }
  assert (Hu : forall i v w, coding_lt M i bound ->
    holds M (v .: i .: rho) substitution_composition_entry_formula ->
    holds M (w .: i .: rho) substitution_composition_entry_formula -> v=w).
  { intros i v w _ Hv Hw. unfold rho in Hv,Hw.
    apply substitution_composition_entry_correct in Hv,Hw.
    exact (substitution_composed_lookup_functional M sb sc sn base eb ec en i v w Hv Hw). }
  destruct (beta_pack_function M rho substitution_composition_entry_formula bound eb Ht Hb Hu)
    as [fb [fc Hpack]].
  exists fb,fc. intros i v Hi. rewrite (environment_lookup_inside M fb fc bound i v Hi).
  rewrite (Hpack i v Hi). unfold rho. apply substitution_composition_entry_correct.
Qed.

Theorem substitution_environment_agreement_total M sb sc sn base eb ec en bound :
  exists fb fc, substitution_environment_agreement M sb sc sn base eb ec en fb fc bound bound.
Proof.
  destruct (substitution_composed_environment_total M sb sc sn base eb ec en bound)
    as [fb [fc Hcomp]]. exists fb,fc. intros i x y z Hi Hix Hxy Hiz.
  apply (proj1 (Hcomp i z Hi)) in Hiz.
  apply (substitution_composed_lookup_functional M sb sc sn base eb ec en i y z); [|exact Hiz].
  exists x. auto.
Qed.

Theorem quotation_substitution_transport_exists M f g bound sb sc sn base eb ec en fresh domain :
  source_bounded M f bound -> numerical_substitution M f sb sc sn base g ->
  exists fb fc,
    substitution_environment_agreement M sb sc sn base eb ec en fb fc bound bound /\
    forall v, numerical_quotation M f fb fc bound fresh domain v <->
      numerical_quotation M g eb ec en fresh domain v.
Proof.
  intros Hbound Hsub.
  destruct (substitution_environment_agreement_total M sb sc sn base eb ec en bound)
    as [fb [fc Hag]]. exists fb,fc. split; [exact Hag|]. intro v. split.
  - intro Hv. destruct (numerical_quotation_total M g eb ec en fresh domain) as [w Hw].
    assert (v=w) by exact (numerical_quotation_substitution M f bound sb sc sn base
      eb ec en fb fc bound fresh domain g v w Hbound Hag Hsub Hv Hw).
    now subst w.
  - intro Hv. destruct (numerical_quotation_total M f fb fc bound fresh domain) as [w Hw].
    assert (w=v) by exact (numerical_quotation_substitution M f bound sb sc sn base
      eb ec en fb fc bound fresh domain g w v Hbound Hag Hsub Hw Hv).
    now subst w.
Qed.

(** Hygiene is a separate conditional property. E's total lookup includes its
    zero-valued tail, so E below fresh also implies zero below fresh. *)
Lemma environment_below_zero M eb ec en fresh :
  environment_below M eb ec en fresh -> coding_lt M (zeroM M) fresh.
Proof.
  intro H. apply (H en (zeroM M)). apply environment_lookup_outside.
  - intro Hi. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax Ha rho => axioms M ax rho Ha) en en Hi eq_refl).
  - reflexivity.
Qed.

Theorem substitution_composed_environment_below M sb sc sn base eb ec en bound fb fc fresh :
  (forall i v, coding_lt M i bound ->
    (environment_lookup M fb fc bound i v <->
     substitution_composed_lookup M sb sc sn base eb ec en i v)) ->
  environment_below M eb ec en fresh -> environment_below M fb fc bound fresh.
Proof.
  intros Hcomp HE i v Hv. destruct (environment_lt_cases M i bound) as [Hi|Hi].
  - apply (proj1 (Hcomp i v Hi)) in Hv. destruct Hv as [x [Hx Hv]]. exact (HE x v Hv).
  - apply (proj1 (environment_lookup_outside M fb fc bound i v Hi)) in Hv. subst v.
    exact (environment_below_zero M eb ec en fresh HE).
Qed.

Theorem quotation_substitution_safe_transport_exists M f g bound sb sc sn base eb ec en fresh domain :
  source_bounded M f bound -> numerical_substitution M f sb sc sn base g ->
  quotation_safe M eb ec en fresh domain ->
  exists fb fc,
    substitution_environment_agreement M sb sc sn base eb ec en fb fc bound bound /\
    quotation_safe M fb fc bound fresh domain /\
    forall v, numerical_quotation M f fb fc bound fresh domain v <->
      numerical_quotation M g eb ec en fresh domain v.
Proof.
  intros Hbound Hsub [Hdomain HE].
  destruct (substitution_composed_environment_total M sb sc sn base eb ec en bound)
    as [fb [fc Hcomp]].
  assert (Hag : substitution_environment_agreement M sb sc sn base eb ec en fb fc bound bound).
  { intros i x y z Hi Hix Hxy Hiz. apply (proj1 (Hcomp i z Hi)) in Hiz.
    apply (substitution_composed_lookup_functional M sb sc sn base eb ec en i y z); [|exact Hiz].
    exists x. auto. }
  exists fb,fc. split; [exact Hag|]. split.
  - split; [exact Hdomain|].
    exact (substitution_composed_environment_below M sb sc sn base eb ec en bound fb fc fresh Hcomp HE).
  - intro v. split.
    + intro Hv. destruct (numerical_quotation_total M g eb ec en fresh domain) as [w Hw].
      assert (v=w) by exact (numerical_quotation_substitution M f bound sb sc sn base
        eb ec en fb fc bound fresh domain g v w Hbound Hag Hsub Hv Hw).
      now subst w.
    + intro Hv. destruct (numerical_quotation_total M f fb fc bound fresh domain) as [w Hw].
      assert (w=v) by exact (numerical_quotation_substitution M f bound sb sc sn base
        eb ec en fb fc bound fresh domain g w v Hbound Hag Hsub Hw Hv).
      now subst w.
Qed.

Lemma substitution_composed_lookup_formula_bound :
  bounded 9 (substitution_composed_lookup_formula $0 $1 $2 $3 $4 $5 $6 $7 $8).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions substitution_composed_lookup_formula_correct.
Print Assumptions substitution_composed_environment_total.
Print Assumptions substitution_environment_agreement_total.
Print Assumptions quotation_substitution_transport_exists.
Print Assumptions substitution_composed_environment_below.
Print Assumptions quotation_substitution_safe_transport_exists.
Print Assumptions substitution_composed_lookup_formula_bound.
