(** Every binder in a numerical quotation is at least its fresh-name base.
    The source code and all environments can be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  NamedBinderFresh NamedBinderConstructors TemplateBinderFresh
  SetFormulaCodes SetCodeDescent NumericalEnvironments
  QuotationPayloads QuotationRules NumericalQuotation QuotationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma quotation_binary_binder_absent M h a b f y :
  quotation_binary M h a b f ->
  named_binder_absent M a y -> named_binder_absent M b y -> named_binder_absent M f y.
Proof.
  intros Hf Ha Hb.
  assert (Hleft : expression_binder_absent M (a .: b .: fun _ => zeroM M) y (CEvar 0)).
  { intros v Hv. change (v=a) in Hv. now subst v. }
  assert (Hright : expression_binder_absent M (a .: b .: fun _ => zeroM M) y (CEvar 1)).
  { intros v Hv. change (v=b) in Hv. now subst v. }
  unfold quotation_binary,quotation_binary_expression in Hf.
  destruct h;
    [exact (expression_binder_absent_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_binder_absent_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_binder_absent_conjunction M _ y _ _ Hleft Hright f Hf)
    |exact (expression_binder_absent_disjunction M _ y _ _ Hleft Hright f Hf)
    |exact (expression_binder_absent_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_binder_absent_implication M _ y _ _ Hleft Hright f Hf)
    |exact (expression_binder_absent_implication M _ y _ _ Hleft Hright f Hf)].
Qed.

Lemma quotation_quantifier_binder_absent M universal k t a f y :
  quotation_quantifier M universal k t a f -> k<>y ->
  named_binder_absent M a y -> named_binder_absent M f y.
Proof.
  intros Hf Hky Ha.
  assert (Hbody : expression_binder_absent M (k .: t .: a .: fun _ => zeroM M) y (CEvar 2)).
  { intros v Hv. change (v=a) in Hv. now subst v. }
  assert (Hbinder : forall v, code_relation M (k .: t .: a .: fun _ => zeroM M) (CEvar 0) v -> v<>y).
  { intros v Hv. change (v=k) in Hv. now subst v. }
  assert (Hguard : expression_binder_absent M (k .: t .: a .: fun _ => zeroM M) y
    (E_wel (CEvar 1) (CEvar 0))).
  { apply expression_binder_absent_atom. now left. }
  unfold quotation_quantifier,quotation_quantifier_expression in Hf. destruct universal.
  - eapply expression_binder_absent_universal; [exact Hbinder| |exact Hf].
    now apply expression_binder_absent_implication.
  - eapply expression_binder_absent_existential; [exact Hbinder| |exact Hf].
    now apply expression_binder_absent_conjunction.
Qed.

Definition quotation_binder_fresh_at M f :=
  forall b c n k t v y,
    numerical_quotation M f b c n k t v -> coding_lt M y k -> named_binder_absent M v y.

Definition quotation_binder_fresh_formula : form :=
  ∀∀∀∀∀∀∀ (numerical_quotation_formula $7 $6 $5 $4 $3 $2 $1 →
    Peano.sless $0 $3 → named_binder_absent_formula $1 $0).

Local Opaque holds numerical_quotation_formula Peano.sless named_binder_absent_formula.
Lemma quotation_binder_fresh_definable M : Definable1 M (quotation_binder_fresh_at M).
Proof.
  exists quotation_binder_fresh_formula,(fun _ => zeroM M). intro f.
  unfold quotation_binder_fresh_formula,quotation_binder_fresh_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite named_binder_absent_formula_correct.
  reflexivity.
Qed.

Lemma quotation_atom_case_binder_fresh M equality a d f :
  sf_relation M (quotation_source_atom equality) a d f -> quotation_binder_fresh_at M f.
Proof.
  intros Hf b c n k t v y Hv Hy.
  destruct (numerical_quotation_atom_inv M equality a d f b c n k t v Hf Hv)
    as [x [z [Hx [Hz Hout]]]].
  exact (quotation_atom_binder_absent M equality x z t k v y Hout Hy).
Qed.

Lemma quotation_binary_binder_fresh M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  quotation_binder_fresh_at M a -> quotation_binder_fresh_at M d -> quotation_binder_fresh_at M f.
Proof.
  intros Hh Hf IHa IHd b c n k t v y Hv Hy.
  destruct (numerical_quotation_binary_inv M h a d f b c n k t v Hh Hf Hv)
    as [x [z [Hx [Hz Hout]]]].
  exact (quotation_binary_binder_absent M h x z v y Hout
    (IHa b c n k t x y Hx Hy) (IHd b c n k t z y Hz Hy)).
Qed.

Lemma quotation_unary_binder_fresh M universal a f :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  quotation_binder_fresh_at M a -> quotation_binder_fresh_at M f.
Proof.
  intros Hf IH b c n k t v y Hv Hy.
  destruct (numerical_quotation_unary_inv M universal a f b c n k t v Hf Hv)
    as [d [e [m [x [Hcons [Hx Hout]]]]]].
  apply (quotation_quantifier_binder_absent M universal k t x v y Hout).
  - intro E. subst k. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) y y Hy eq_refl).
  - exact (IH d e m (succM M k) t x y Hx
      (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k))).
Qed.

Theorem numerical_quotation_binder_fresh M f : quotation_binder_fresh_at M f.
Proof.
  revert f. apply (sf_code_induction M (quotation_binder_fresh_at M)).
  - apply quotation_binder_fresh_definable.
  - intros b c n k t v y Hv Hy.
    rewrite (numerical_quotation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) Hv).
    apply named_binder_absent_one.
  - intros f Hbad b c n k t v y Hv Hy.
    rewrite (numerical_quotation_invalid M f b c n k t v (or_intror Hbad) Hv).
    apply named_binder_absent_one.
  - intros a d f Hf. exact (quotation_atom_case_binder_fresh M false a d f Hf).
  - intros a d f Hf. exact (quotation_atom_case_binder_fresh M true a d f Hf).
  - exact (quotation_binary_binder_fresh M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (quotation_unary_binder_fresh M true a f Hf IH).
    + exact (quotation_unary_binder_fresh M false a f Hf IH).
Qed.

Corollary numerical_quotation_matrix_binder_absent M f b c n k t v :
  numerical_quotation M f b c n (succM M k) t v -> named_binder_absent M v k.
Proof.
  intro H. exact (numerical_quotation_binder_fresh M f b c n (succM M k) t v k H (coding_lt_succ M k)).
Qed.

Corollary numerical_quotation_no_low_binder M f b c n k t v g y p :
  numerical_quotation M f b c n k t v -> formula_reaches M v g ->
  tagged_pair_graph M 2 y p g -> ~coding_lt M y k.
Proof.
  intros Hq Hr Hb Hlt. exact (numerical_quotation_binder_fresh M f b c n k t v y Hq Hlt g p Hr Hb).
Qed.

Print Assumptions quotation_binder_fresh_definable.
Print Assumptions numerical_quotation_binder_fresh.
Print Assumptions numerical_quotation_matrix_binder_absent.
Print Assumptions numerical_quotation_no_low_binder.
