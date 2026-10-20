(** Uniform substitution/quotation composition. All source codes, bounds,
    environments and trace lengths are arbitrary PA-model elements.
    The conclusion is literal equality at the same fresh/domain parameters. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent SourceBounded
  NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution SubstitutionPayloads
  NumericalQuotation QuotationFunctionality QuotationPayloads QuotationRules
  QuotationBoundedEnvironment SubstitutionEnvironment.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_substitution_at M f :=
  forall bound sb sc sn base eb ec en fb fc fn fresh domain g v w,
  source_bounded M f bound ->
  substitution_environment_agreement M sb sc sn base eb ec en fb fc fn bound ->
  numerical_substitution M f sb sc sn base g ->
  numerical_quotation M f fb fc fn fresh domain v ->
  numerical_quotation M g eb ec en fresh domain w -> v=w.

(** Sixteen slots: bound15, sb14, sc13, sn12, base11, eb10, ec9, en8,
    fb7, fc6, fn5, fresh4, domain3, g2, v1, w0. Source f remains at16. *)
Definition quotation_substitution_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀
    (source_bounded_accept_formula $16 $15 →
     substitution_environment_agreement_formula $14 $13 $12 $11
       $10 $9 $8 $7 $6 $5 $15 →
     numerical_substitution_formula $16 $14 $13 $12 $11 $2 →
     numerical_quotation_formula $16 $7 $6 $5 $4 $3 $1 →
     numerical_quotation_formula $2 $10 $9 $8 $4 $3 $0 → $1 == $0).

Local Opaque holds source_bounded_accept_formula
  substitution_environment_agreement_formula numerical_substitution_formula
  numerical_quotation_formula.
Lemma quotation_substitution_at_definable M : Definable1 M (quotation_substitution_at M).
Proof.
  exists quotation_substitution_formula,(fun _ => zeroM M). intro f.
  unfold quotation_substitution_formula,quotation_substitution_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite substitution_environment_agreement_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct. reflexivity.
Qed.

Lemma quotation_substitution_atom M equality a d f :
  sf_relation M (quotation_source_atom equality) a d f -> quotation_substitution_at M f.
Proof.
  intros Hf bound sb sc sn base eb ec en fb fc fn fresh domain g v w
    Hb Hag Hsub Hfv Hgw.
  assert (Hatom : quotation_source_atom equality=SFMember \/
    quotation_source_atom equality=SFEqual) by (destruct equality;cbn;auto).
  destruct (proj1 (source_bounded_accept_atom M _ a d f bound Hatom Hf) Hb) as [Ha Hd].
  assert (Hsf : sf_relation M (substitution_source_atom equality) a d f).
  { destruct equality; exact Hf. }
  destruct (proj1 (numerical_substitution_atom M equality a d f sb sc sn base g Hsf) Hsub)
    as [x [y [Hax [Hdy Hg]]]].
  assert (Hgq : sf_relation M (quotation_source_atom equality) x y g).
  { destruct equality; exact Hg. }
  destruct (numerical_quotation_atom_inv M equality a d f fb fc fn fresh domain v Hf Hfv)
    as [av [dv [Hav [Hdv Hv]]]].
  destruct (numerical_quotation_atom_inv M equality x y g eb ec en fresh domain w Hgq Hgw)
    as [xv [yv [Hxv [Hyv Hw]]]].
  assert (Ex : xv=av) by exact (Hag a x xv av Ha Hax Hxv Hav).
  assert (Ey : yv=dv) by exact (Hag d y yv dv Hd Hdy Hyv Hdv).
  subst xv yv. exact (quotation_atom_functional M equality av dv domain fresh v w Hv Hw).
Qed.

Lemma quotation_substitution_binary M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  quotation_substitution_at M a -> quotation_substitution_at M d ->
  quotation_substitution_at M f.
Proof.
  intros Hh Hf IHa IHd bound sb sc sn base eb ec en fb fc fn fresh domain g v w
    Hb Hag Hsub Hfv Hgw.
  destruct (proj1 (source_bounded_accept_binary M h a d f bound Hh Hf) Hb) as [Ha Hd].
  destruct (proj1 (numerical_substitution_binary M h a d f sb sc sn base g Hh Hf) Hsub)
    as [x [y [Hax [Hdy Hg]]]].
  destruct (numerical_quotation_binary_inv M h a d f fb fc fn fresh domain v Hh Hf Hfv)
    as [av [dv [Hav [Hdv Hv]]]].
  destruct (numerical_quotation_binary_inv M h x y g eb ec en fresh domain w Hh Hg Hgw)
    as [xv [yv [Hxv [Hyv Hw]]]].
  assert (Ex : av=xv) by exact
    (IHa bound sb sc sn base eb ec en fb fc fn fresh domain x av xv Ha Hag Hax Hav Hxv).
  assert (Ey : dv=yv) by exact
    (IHd bound sb sc sn base eb ec en fb fc fn fresh domain y dv yv Hd Hag Hdy Hdv Hyv).
  subst xv yv. exact (quotation_binary_functional M h av dv v w Hv Hw).
Qed.

Lemma quotation_substitution_unary M universal a f :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  quotation_substitution_at M a -> quotation_substitution_at M f.
Proof.
  intros Hf IH bound sb sc sn base eb ec en fb fc fn fresh domain g v w
    Hb Hag Hsub Hfv Hgw.
  assert (Hquant : quotation_source_quantifier universal=SFAll \/
    quotation_source_quantifier universal=SFEx) by (destruct universal;cbn;auto).
  apply (proj1 (source_bounded_accept_unary M _ a f bound Hquant Hf)) in Hb.
  assert (Hsf : sf_relation M (substitution_source_quantifier universal) a (zeroM M) f).
  { destruct universal; exact Hf. }
  destruct (proj1 (numerical_substitution_quantifier M universal a f sb sc sn base g Hsf) Hsub)
    as [sb' [sc' [sn' [x [Hlift [Hax Hg]]]]]].
  assert (Hgq : sf_relation M (quotation_source_quantifier universal) x (zeroM M) g).
  { destruct universal; exact Hg. }
  destruct (numerical_quotation_unary_inv M universal a f fb fc fn fresh domain v Hf Hfv)
    as [fb' [fc' [fn' [av [HF [Hav Hv]]]]]].
  destruct (numerical_quotation_unary_inv M universal x g eb ec en fresh domain w Hgq Hgw)
    as [eb' [ec' [en' [xv [HE [Hxv Hw]]]]]].
  assert (Hag' : substitution_environment_agreement M sb' sc' sn' (succM M base)
      eb' ec' en' fb' fc' fn' (succM M bound)).
  { exact (substitution_environment_agreement_lift M sb sc sn base eb ec en fb fc fn
      bound fresh sb' sc' sn' eb' ec' en' fb' fc' fn' Hag Hlift HE HF). }
  assert (Ex : av=xv) by exact
    (IH (succM M bound) sb' sc' sn' (succM M base) eb' ec' en' fb' fc' fn'
      (succM M fresh) domain x av xv Hb Hag' Hax Hav Hxv).
  subst xv. exact (quotation_quantifier_functional M universal fresh domain av v w Hv Hw).
Qed.

Theorem numerical_quotation_substitution M f : quotation_substitution_at M f.
Proof.
  revert f. apply (sf_code_induction M (quotation_substitution_at M)).
  - apply quotation_substitution_at_definable.
  - intros bound sb sc sn base eb ec en fb fc fn fresh domain g v w
      Hb Hag Hsub Hv Hw.
    apply (proj1 (numerical_substitution_invalid M (zeroM M) sb sc sn base g
      (or_introl eq_refl))) in Hsub. subst g.
    rewrite (numerical_quotation_invalid M (zeroM M) fb fc fn fresh domain v
      (or_introl eq_refl) Hv),
      (numerical_quotation_invalid M (zeroM M) eb ec en fresh domain w
      (or_introl eq_refl) Hw). reflexivity.
  - intros f Hbad bound sb sc sn base eb ec en fb fc fn fresh domain g v w Hb.
    exfalso. exact (source_bounded_reject_invalid M f bound Hbad Hb).
  - intros a d f Hf. exact (quotation_substitution_atom M false a d f Hf).
  - intros a d f Hf. exact (quotation_substitution_atom M true a d f Hf).
  - exact (quotation_substitution_binary M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (quotation_substitution_unary M true a f Hf IH).
    + exact (quotation_substitution_unary M false a f Hf IH).
Qed.

Corollary numerical_quotation_substitution_closed M f sb sc sn base
    eb ec en fb fc fn fresh domain g v w :
  source_bounded M f (zeroM M) ->
  numerical_substitution M f sb sc sn base g ->
  numerical_quotation M f fb fc fn fresh domain v ->
  numerical_quotation M g eb ec en fresh domain w -> v=w.
Proof.
  intros Hb Hsub Hv Hw. apply (numerical_quotation_substitution M f (zeroM M)
    sb sc sn base eb ec en fb fc fn fresh domain g v w Hb); [|exact Hsub|exact Hv|exact Hw].
  intros i x y z Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Lemma quotation_substitution_formula_bound : bounded 1 quotation_substitution_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions quotation_substitution_at_definable.
Print Assumptions numerical_quotation_substitution.
Print Assumptions numerical_quotation_substitution_closed.
Print Assumptions quotation_substitution_formula_bound.
