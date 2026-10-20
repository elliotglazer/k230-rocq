(** Full syntactic freshness of numerical quotient outputs. The assumptions
    exclude the raw zero name, the fixed domain, and every source-environment
    name; all newly introduced binders are above the excluded name. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  FormulaFreshConstructors TemplateFormulaFresh
  SetFormulaCodes SetCodeDescent NumericalEnvironments
  QuotationPayloads QuotationRules NumericalQuotation QuotationFunctionality QuotationHygiene.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_environment_avoids M b c n y :=
  forall i u, environment_lookup M b c n i u -> u<>y.
Definition quotation_environment_avoids_formula (b c n y : term) : form :=
  ∀∀ (environment_lookup_formula (code_lift2 b) (code_lift2 c) (code_lift2 n) $1 $0 →
    ¬ ($0 == code_lift2 y)).

Local Opaque holds environment_lookup_formula.
Lemma quotation_holds_false M rho : holds M rho ⊥ <-> False.
Proof. reflexivity. Qed.

Lemma quotation_environment_avoids_formula_correct M rho b c n y :
  holds M rho (quotation_environment_avoids_formula b c n y) <->
  quotation_environment_avoids M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho y).
Proof.
  unfold quotation_environment_avoids_formula,quotation_environment_avoids.
  repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite fresh_holds_eq. setoid_rewrite quotation_holds_false.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Lemma quotation_environment_avoids_cons M b c n k d e m y :
  quotation_environment_avoids M b c n y -> k<>y ->
  environment_cons M b c n k d e m -> quotation_environment_avoids M d e m y.
Proof.
  intros Henv Hky Hcons i u Hu.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [Hi|[j Hi]]; subst i.
  - apply (environment_cons_head M b c n k d e m u Hcons) in Hu. now subst u.
  - apply (environment_cons_tail M b c n k d e m j u Hcons) in Hu. exact (Henv j u Hu).
Qed.

Lemma quotation_binary_fresh M h a b f y :
  quotation_binary M h a b f -> y<>zeroM M ->
  formula_fresh M a y -> formula_fresh M b y -> formula_fresh M f y.
Proof.
  intros Hf Hy Ha Hb.
  assert (Hleft : expression_fresh M (a .: b .: fun _ => zeroM M) y (CEvar 0)).
  { intros v Hv. change (v=a) in Hv. now subst v. }
  assert (Hright : expression_fresh M (a .: b .: fun _ => zeroM M) y (CEvar 1)).
  { intros v Hv. change (v=b) in Hv. now subst v. }
  unfold quotation_binary,quotation_binary_expression in Hf.
  destruct h;
    [exact (expression_fresh_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_fresh_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_fresh_conjunction M _ y _ _ Hy Hleft Hright f Hf)
    |exact (expression_fresh_disjunction M _ y _ _ Hy Hleft Hright f Hf)
    |exact (expression_fresh_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_fresh_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_fresh_implication M _ y _ _ Hleft Hright f Hf)].
Qed.

Lemma quotation_quantifier_fresh M universal k t a f y :
  quotation_quantifier M universal k t a f -> y<>zeroM M -> k<>y -> t<>y ->
  formula_fresh M a y -> formula_fresh M f y.
Proof.
  intros Hf Hzero Hky Hty Ha.
  assert (Hbody : expression_fresh M (k .: t .: a .: fun _ => zeroM M) y (CEvar 2)).
  { intros v Hv. change (v=a) in Hv. now subst v. }
  assert (Hbinder : expression_name_avoids M (k .: t .: a .: fun _ => zeroM M) y (CEvar 0)).
  { intros v Hv. change (v=k) in Hv. now subst v. }
  assert (Hdomain : expression_name_avoids M (k .: t .: a .: fun _ => zeroM M) y (CEvar 1)).
  { intros v Hv. change (v=t) in Hv. now subst v. }
  assert (Hguard : expression_fresh M (k .: t .: a .: fun _ => zeroM M) y
    (E_wel (CEvar 1) (CEvar 0))).
  { apply expression_fresh_atom; [now left|exact Hdomain|exact Hbinder]. }
  unfold quotation_quantifier,quotation_quantifier_expression in Hf. destruct universal.
  - eapply expression_fresh_universal; [exact Hbinder| |exact Hf].
    now apply expression_fresh_implication.
  - eapply expression_fresh_existential; [exact Hzero|exact Hbinder| |exact Hf].
    now apply expression_fresh_conjunction.
Qed.

Definition quotation_formula_fresh_at M f :=
  forall b c n k t v y,
    numerical_quotation M f b c n k t v -> coding_lt M y k ->
    y<>zeroM M -> y<>t -> quotation_environment_avoids M b c n y -> formula_fresh M v y.

Definition quotation_formula_fresh_formula : form :=
  ∀∀∀∀∀∀∀ (numerical_quotation_formula $7 $6 $5 $4 $3 $2 $1 →
    Peano.sless $0 $3 → ¬ ($0 == zero) → ¬ ($0 == $2) →
    quotation_environment_avoids_formula $6 $5 $4 $0 → formula_fresh_formula $1 $0).

Local Opaque numerical_quotation_formula Peano.sless quotation_environment_avoids_formula
  formula_fresh_formula.
Lemma quotation_formula_fresh_definable M : Definable1 M (quotation_formula_fresh_at M).
Proof.
  exists quotation_formula_fresh_formula,(fun _ => zeroM M). intro f.
  unfold quotation_formula_fresh_formula,quotation_formula_fresh_at.
  repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp.
  setoid_rewrite numerical_quotation_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite quotation_environment_avoids_formula_correct.
  setoid_rewrite fresh_holds_eq. setoid_rewrite quotation_holds_false.
  setoid_rewrite formula_fresh_formula_correct. reflexivity.
Qed.

Lemma quotation_atom_case_fresh M equality a d f :
  sf_relation M (quotation_source_atom equality) a d f -> quotation_formula_fresh_at M f.
Proof.
  intros Hf b c n k t v y Hv Hy Hzero Hyt Henv.
  destruct (numerical_quotation_atom_inv M equality a d f b c n k t v Hf Hv)
    as [x [z [Hx [Hz Hout]]]].
  apply (quotation_atom_fresh M equality x z t k v y Hout Hy Hzero).
  - exact (Henv a x Hx).
  - exact (Henv d z Hz).
  - intro E. apply Hyt. symmetry. exact E.
Qed.

Lemma quotation_binary_formula_fresh M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  quotation_formula_fresh_at M a -> quotation_formula_fresh_at M d -> quotation_formula_fresh_at M f.
Proof.
  intros Hh Hf IHa IHd b c n k t v y Hv Hy Hzero Hyt Henv.
  destruct (numerical_quotation_binary_inv M h a d f b c n k t v Hh Hf Hv)
    as [x [z [Hx [Hz Hout]]]].
  exact (quotation_binary_fresh M h x z v y Hout Hzero
    (IHa b c n k t x y Hx Hy Hzero Hyt Henv)
    (IHd b c n k t z y Hz Hy Hzero Hyt Henv)).
Qed.

Lemma quotation_unary_formula_fresh M universal a f :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  quotation_formula_fresh_at M a -> quotation_formula_fresh_at M f.
Proof.
  intros Hf IH b c n k t v y Hv Hy Hzero Hyt Henv.
  destruct (numerical_quotation_unary_inv M universal a f b c n k t v Hf Hv)
    as [d [e [m [x [Hcons [Hx Hout]]]]]].
  assert (Hky : k<>y).
  { intro E. subst k. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) y y Hy eq_refl). }
  apply (quotation_quantifier_fresh M universal k t x v y Hout Hzero Hky).
  - intro E. apply Hyt. symmetry. exact E.
  - apply (IH d e m (succM M k) t x y Hx).
    + exact (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k)).
    + exact Hzero.
    + exact Hyt.
    + exact (quotation_environment_avoids_cons M b c n k d e m y Henv Hky Hcons).
Qed.

Theorem numerical_quotation_formula_fresh M f : quotation_formula_fresh_at M f.
Proof.
  revert f. apply (sf_code_induction M (quotation_formula_fresh_at M)).
  - apply quotation_formula_fresh_definable.
  - intros b c n k t v y Hv Hy Hzero Hyt Henv.
    rewrite (numerical_quotation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) Hv).
    now apply formula_fresh_one.
  - intros f Hbad b c n k t v y Hv Hy Hzero Hyt Henv.
    rewrite (numerical_quotation_invalid M f b c n k t v (or_intror Hbad) Hv).
    now apply formula_fresh_one.
  - intros a d f Hf. exact (quotation_atom_case_fresh M false a d f Hf).
  - intros a d f Hf. exact (quotation_atom_case_fresh M true a d f Hf).
  - exact (quotation_binary_formula_fresh M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (quotation_unary_formula_fresh M true a f Hf IH).
    + exact (quotation_unary_formula_fresh M false a f Hf IH).
Qed.

(** This uses the original parent environment, not its extension by k. *)
Corollary numerical_quotation_parent_fresh M f b c n k t v :
  quotation_safe M b c n k t ->
  numerical_quotation M f b c n (succM M k) t v -> formula_fresh M v k.
Proof.
  intros [Ht Henv] Hq.
  apply (numerical_quotation_formula_fresh M f b c n (succM M k) t v k Hq (coding_lt_succ M k)).
  - intro E. rewrite E in Ht. exact (coding_not_lt_zero M t Ht).
  - intro E. rewrite E in Ht. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) t t Ht eq_refl).
  - intros i u Hu. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) u k (Henv i u Hu)).
Qed.

Print Assumptions quotation_environment_avoids_formula_correct.
Print Assumptions quotation_environment_avoids_cons.
Print Assumptions quotation_formula_fresh_definable.
Print Assumptions numerical_quotation_formula_fresh.
Print Assumptions numerical_quotation_parent_fresh.
