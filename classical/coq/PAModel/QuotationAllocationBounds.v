(** A PA-definable interval containing every binder allocated by quotation.
    The source code bounds the number of source quantifiers; a fixed margin
    covers the binders in the two finite quotient atom templates. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
  CodeExpressions CodeDescent NumericalProofs SetFormulaCodes SetCodeDescent
  NamedBinderFresh TemplateBinderFresh TemplateBinderRange TemplateNamedExclusions
  FiniteTemplateEvaluation QuotationAtomRebase QuotientAtomTemplates
  QuotationPayloads QuotationRules NumericalQuotation QuotationFunctionality
  QuotationBinderFresh.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_allocation_margin : nat := S
  (template_binder_span (source_deqv $0 $1 $2) + template_binder_span (source_dmem $0 $1 $2)).
Definition quotation_allocation_avoids M source k y :=
  forall d,coding_lt M d (addM M source (code_numeral M quotation_allocation_margin)) ->
    addM M k d <> y.

Definition quotation_allocation_avoids_formula (source k y : term) : form :=
  ∀ (Peano.sless $0 ((source ⊕ num quotation_allocation_margin)`[↑]) →
    ¬ ((k`[↑] ⊕ $0) == y`[↑])).

Local Opaque holds Peano.sless.
Lemma allocation_eval_add M rho a b :
  evalM M rho (a ⊕ b) = addM M (evalM M rho a) (evalM M rho b).
Proof. reflexivity. Qed.
Lemma allocation_eval_shift M rho d t :
  evalM M (d .: rho) t`[↑] = evalM M rho t.
Proof. unfold evalM. apply eval_up. Qed.
Lemma quotation_allocation_avoids_correct M rho source k y :
  holds M rho (quotation_allocation_avoids_formula source k y) <->
  quotation_allocation_avoids M (evalM M rho source) (evalM M rho k) (evalM M rho y).
Proof.
  unfold quotation_allocation_avoids_formula,quotation_allocation_avoids.
  rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct. setoid_rewrite code_holds_neq.
  setoid_rewrite allocation_eval_shift. setoid_rewrite allocation_eval_add.
  setoid_rewrite allocation_eval_shift. setoid_rewrite code_eval_num. reflexivity.
Qed.

Lemma allocation_cap_extend M d cap source :
  coding_lt M d cap -> coding_lt M d (addM M source cap).
Proof.
  intros [u Hu]. exists (addM M source u). rewrite Hu.
  rewrite (Arithmetic.add_comm M source),Arithmetic.add_succ.
  f_equal. now rewrite <- (Arithmetic.add_assoc M d u source), (Arithmetic.add_comm M u source).
Qed.

Lemma quotation_allocation_head M source k y :
  quotation_allocation_avoids M source k y -> k<>y.
Proof.
  intro H. specialize (H (zeroM M)). rewrite (coding_add_zero_r M) in H.
  apply H. apply allocation_cap_extend.
  apply (sf_numeral_lt M 0 quotation_allocation_margin).
  unfold quotation_allocation_margin. lia.
Qed.

Lemma quotation_allocation_subformula M a source k y :
  coding_lt M a source -> quotation_allocation_avoids M source k y ->
  quotation_allocation_avoids M a k y.
Proof.
  intros Ha H d Hd. apply H.
  eapply coding_lt_trans;[exact Hd|].
  rewrite (Arithmetic.add_comm M a),(Arithmetic.add_comm M source).
  now apply coding_lt_add_left.
Qed.

Section SuccessorRange.
Variable M : Model.
Add Ring allocation_bound_ring : (model_semiring M).
Lemma allocation_child_index d a source cap :
  coding_lt M d (addM M a cap) -> coding_lt M a source ->
  coding_lt M (succM M d) (addM M source cap).
Proof.
  intros [u Hu] [v Hv]. exists (addM M u v).
  rewrite Hv,Arithmetic.add_succ.
  assert (E : addM M (addM M a v) cap = addM M (addM M a cap) v) by ring.
  rewrite E,Hu. f_equal. rewrite !Arithmetic.add_succ. f_equal. ring.
Qed.

Lemma quotation_allocation_child a source k y :
  coding_lt M a source -> quotation_allocation_avoids M source k y ->
  quotation_allocation_avoids M a (succM M k) y.
Proof.
  intros Ha H d Hd.
  specialize (H (succM M d) (allocation_child_index d a source
    (code_numeral M quotation_allocation_margin) Hd Ha)).
  replace (addM M (succM M k) d) with (addM M k (succM M d));[exact H|].
  rewrite (succ_as_add M k),(succ_as_add M d). ring.
Qed.
End SuccessorRange.

Lemma quotation_atom_allocation_span (equality : bool) :
  template_binder_span
    (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2)
  < quotation_allocation_margin.
Proof. destruct equality;unfold quotation_allocation_margin;lia. Qed.

Lemma quotation_atom_allocation_avoids M equality x z domain k v source y :
  quotation_atom M equality x z domain k v ->
  quotation_allocation_avoids M source k y -> named_binder_absent M v y.
Proof.
  intros HQ HR.
  apply (template_evaluation_binder_exclusion M
    (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2)
    (quotation_atom_values x z domain) k y v).
  - apply template_allocations_avoid_offsets. intros i Hi.
    apply HR. apply allocation_cap_extend.
    apply sf_numeral_lt. pose proof (quotation_atom_allocation_span equality). lia.
  - exact (proj1 (quotation_atom_evaluation M equality x z domain k v) HQ).
Qed.

Definition quotation_allocation_binder_at M source :=
  forall b c n k t v y,numerical_quotation M source b c n k t v ->
    quotation_allocation_avoids M source k y -> named_binder_absent M v y.
Definition quotation_allocation_binder_formula : form :=
  ∀∀∀∀∀∀∀ (numerical_quotation_formula $7 $6 $5 $4 $3 $2 $1 →
    quotation_allocation_avoids_formula $7 $3 $0 → named_binder_absent_formula $1 $0).
Local Opaque numerical_quotation_formula quotation_allocation_avoids_formula named_binder_absent_formula.
Lemma quotation_allocation_binder_definable M : Definable1 M (quotation_allocation_binder_at M).
Proof.
  exists quotation_allocation_binder_formula,(fun _=>zeroM M). intro source.
  unfold quotation_allocation_binder_formula,quotation_allocation_binder_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite quotation_allocation_avoids_correct.
  setoid_rewrite named_binder_absent_formula_correct. reflexivity.
Qed.

Lemma quotation_allocation_atom M equality a d source :
  sf_relation M (quotation_source_atom equality) a d source -> quotation_allocation_binder_at M source.
Proof.
  intros HS b c n k t v y HQ HR.
  destruct (numerical_quotation_atom_inv M equality a d source b c n k t v HS HQ)
    as [x [z [HX [HZ Hout]]]].
  exact (quotation_atom_allocation_avoids M equality x z t k v source y Hout HR).
Qed.

Lemma quotation_allocation_binary M h a d source :
  sf_binary h -> sf_relation M h a d source ->
  quotation_allocation_binder_at M a -> quotation_allocation_binder_at M d ->
  quotation_allocation_binder_at M source.
Proof.
  intros Hh HS IHa IHd b c n k t v y HQ HR.
  destruct (sf_relation_descent M h a d source HS) as [Ha Hd].
  destruct (numerical_quotation_binary_inv M h a d source b c n k t v Hh HS HQ)
    as [x [z [HX [HZ Hout]]]].
  apply (quotation_binary_binder_absent M h x z v y Hout).
  - apply (IHa b c n k t x y HX). exact (quotation_allocation_subformula M a source k y Ha HR).
  - apply (IHd b c n k t z y HZ).
    apply (quotation_allocation_subformula M d source k y);[|exact HR].
    destruct Hh as [Hh|[Hh|Hh]];subst h;exact Hd.
Qed.

Lemma quotation_allocation_unary M universal a source :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) source ->
  quotation_allocation_binder_at M a -> quotation_allocation_binder_at M source.
Proof.
  intros HS IH b c n k t v y HQ HR.
  destruct (numerical_quotation_unary_inv M universal a source b c n k t v HS HQ)
    as [d [e [m [x [HC [HX Hout]]]]]].
  apply (quotation_quantifier_binder_absent M universal k t x v y Hout).
  - exact (quotation_allocation_head M source k y HR).
  - apply (IH d e m (succM M k) t x y HX).
    apply (quotation_allocation_child M a source k y);[|exact HR].
    exact (proj1 (sf_relation_descent M (quotation_source_quantifier universal) a (zeroM M) source HS)).
Qed.

Theorem numerical_quotation_allocation_binder M source : quotation_allocation_binder_at M source.
Proof.
  revert source. apply (sf_code_induction M (quotation_allocation_binder_at M)).
  - apply quotation_allocation_binder_definable.
  - intros b c n k t v y HQ HR.
    rewrite (numerical_quotation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) HQ).
    apply named_binder_absent_one.
  - intros source Hbad b c n k t v y HQ HR.
    rewrite (numerical_quotation_invalid M source b c n k t v (or_intror Hbad) HQ).
    apply named_binder_absent_one.
  - intros a d source HS. exact (quotation_allocation_atom M false a d source HS).
  - intros a d source HS. exact (quotation_allocation_atom M true a d source HS).
  - exact (quotation_allocation_binary M).
  - intros h a source Hh HS IH. destruct Hh as [Hh|Hh];subst h.
    + exact (quotation_allocation_unary M true a source HS IH).
    + exact (quotation_allocation_unary M false a source HS IH).
Qed.

Print Assumptions quotation_allocation_avoids_correct.
Print Assumptions numerical_quotation_allocation_binder.
