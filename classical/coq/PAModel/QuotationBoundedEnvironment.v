(** A bounded source formula only reads its live environment entries.  In
    particular, quotation of a closed source formula is independent of the
    entire external environment, even for nonstandard source codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalEnvironmentExt SourceBounded
  NumericalQuotation QuotationFunctionality QuotationPayloads QuotationRules.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition bounded_environment_agreement M b c n d e m k :=
  forall i v w, coding_lt M i k ->
    environment_lookup M b c n i v -> environment_lookup M d e m i w -> v=w.

Definition bounded_environment_agreement_formula (b c n d e m k : term) : form :=
  ∀∀∀ (Peano.sless $2 (k`[↑]`[↑]`[↑]) →
    environment_lookup_formula (b`[↑]`[↑]`[↑]) (c`[↑]`[↑]`[↑])
      (n`[↑]`[↑]`[↑]) $2 $1 →
    environment_lookup_formula (d`[↑]`[↑]`[↑]) (e`[↑]`[↑]`[↑])
      (m`[↑]`[↑]`[↑]) $2 $0 → $1 == $0).

Local Opaque holds environment_lookup_formula Peano.sless.
Lemma bounded_environment_agreement_formula_correct M rho b c n d e m k :
  holds M rho (bounded_environment_agreement_formula b c n d e m k) <->
  bounded_environment_agreement M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m) (evalM M rho k).
Proof.
  unfold bounded_environment_agreement_formula,bounded_environment_agreement.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct.
  setoid_rewrite environment_lookup_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma bounded_environment_agreement_cons M b c n d e m k x b' c' n' d' e' m' :
  bounded_environment_agreement M b c n d e m k ->
  environment_cons M b c n x b' c' n' ->
  environment_cons M d e m x d' e' m' ->
  bounded_environment_agreement M b' c' n' d' e' m' (succM M k).
Proof.
  intros H Hc Hd i v w Hi Hv Hw.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax Ha rho => axioms M ax rho Ha) i) as [Ei|[j Ei]]; subst i.
  - apply (environment_cons_head M b c n x b' c' n' v Hc) in Hv.
    apply (environment_cons_head M d e m x d' e' m' w Hd) in Hw. congruence.
  - apply (environment_cons_tail M b c n x b' c' n' j v Hc) in Hv.
    apply (environment_cons_tail M d e m x d' e' m' j w Hd) in Hw.
    exact (H j v w (proj1 (coding_lt_succ_cancel M j k) Hi) Hv Hw).
Qed.

Definition quotation_bounded_environment_at M f :=
  forall bound b c n d e m k t v w,
    source_bounded M f bound -> bounded_environment_agreement M b c n d e m bound ->
    numerical_quotation M f b c n k t v -> numerical_quotation M f d e m k t w -> v=w.

(** The eleven bound variables are bound,b,c,n,d,e,m,k,t,v,w. *)
Definition quotation_bounded_environment_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀
    (source_bounded_accept_formula $11 $10 →
     bounded_environment_agreement_formula $9 $8 $7 $6 $5 $4 $10 →
     numerical_quotation_formula $11 $9 $8 $7 $3 $2 $1 →
     numerical_quotation_formula $11 $6 $5 $4 $3 $2 $0 → $1 == $0).

Local Opaque source_bounded_accept_formula bounded_environment_agreement_formula
  numerical_quotation_formula.
Lemma quotation_bounded_environment_definable M :
  Definable1 M (quotation_bounded_environment_at M).
Proof.
  exists quotation_bounded_environment_formula,(fun _ => zeroM M). intro f.
  unfold quotation_bounded_environment_formula,quotation_bounded_environment_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite bounded_environment_agreement_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct. reflexivity.
Qed.

Lemma quotation_bounded_environment_atom M equality a d f :
  sf_relation M (quotation_source_atom equality) a d f ->
  quotation_bounded_environment_at M f.
Proof.
  intros Hf bound b c n b' c' n' k t v w Hb Heq Hv Hw.
  assert (Hatom : quotation_source_atom equality=SFMember \/
    quotation_source_atom equality=SFEqual) by (destruct equality;cbn;auto).
  apply (proj1 (source_bounded_accept_atom M _ a d f bound Hatom Hf)) in Hb.
  destruct Hb as [Ha Hd].
  destruct (numerical_quotation_atom_inv M equality a d f b c n k t v Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (numerical_quotation_atom_inv M equality a d f b' c' n' k t w Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (Heq a x x' Ha Hx Hx').
  assert (Ey : y=y') by exact (Heq d y y' Hd Hy Hy').
  subst x' y'. exact (quotation_atom_functional M equality x y t k v w Hout Hout').
Qed.

Lemma quotation_bounded_environment_binary M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  quotation_bounded_environment_at M a -> quotation_bounded_environment_at M d ->
  quotation_bounded_environment_at M f.
Proof.
  intros Hh Hf IHa IHd bound b c n b' c' n' k t v w Hb Heq Hv Hw.
  apply (proj1 (source_bounded_accept_binary M h a d f bound Hh Hf)) in Hb.
  destruct Hb as [Ha Hd].
  destruct (numerical_quotation_binary_inv M h a d f b c n k t v Hh Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (numerical_quotation_binary_inv M h a d f b' c' n' k t w Hh Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (IHa bound b c n b' c' n' k t x x' Ha Heq Hx Hx').
  assert (Ey : y=y') by exact (IHd bound b c n b' c' n' k t y y' Hd Heq Hy Hy').
  subst x' y'. exact (quotation_binary_functional M h x y v w Hout Hout').
Qed.

Lemma quotation_bounded_environment_unary M universal a f :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  quotation_bounded_environment_at M a -> quotation_bounded_environment_at M f.
Proof.
  intros Hf IH bound b c n b' c' n' k t v w Hb Heq Hv Hw.
  assert (Hquant : quotation_source_quantifier universal=SFAll \/
    quotation_source_quantifier universal=SFEx) by (destruct universal;cbn;auto).
  apply (proj1 (source_bounded_accept_unary M _ a f bound Hquant Hf)) in Hb.
  destruct (numerical_quotation_unary_inv M universal a f b c n k t v Hf Hv)
    as [d [e [m [x [Hcons [Hx Hout]]]]]].
  destruct (numerical_quotation_unary_inv M universal a f b' c' n' k t w Hf Hw)
    as [d' [e' [m' [y [Hcons' [Hy Hout']]]]]].
  assert (Hchild : bounded_environment_agreement M d e m d' e' m' (succM M bound)).
  { exact (bounded_environment_agreement_cons M b c n b' c' n' bound k
      d e m d' e' m' Heq Hcons Hcons'). }
  assert (Ex : x=y) by exact (IH (succM M bound) d e m d' e' m'
    (succM M k) t x y Hb Hchild Hx Hy).
  subst y. exact (quotation_quantifier_functional M universal k t x v w Hout Hout').
Qed.

Theorem numerical_quotation_bounded_environment M f : quotation_bounded_environment_at M f.
Proof.
  revert f. apply (sf_code_induction M (quotation_bounded_environment_at M)).
  - apply quotation_bounded_environment_definable.
  - intros bound b c n d e m k t v w Hb Heq Hv Hw.
    rewrite (numerical_quotation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) Hv),
      (numerical_quotation_invalid M (zeroM M) d e m k t w (or_introl eq_refl) Hw).
    reflexivity.
  - intros f Hbad bound b c n d e m k t v w Hb.
    exfalso. exact (source_bounded_reject_invalid M f bound Hbad Hb).
  - intros a d f Hf. exact (quotation_bounded_environment_atom M false a d f Hf).
  - intros a d f Hf. exact (quotation_bounded_environment_atom M true a d f Hf).
  - exact (quotation_bounded_environment_binary M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh];subst h.
    + exact (quotation_bounded_environment_unary M true a f Hf IH).
    + exact (quotation_bounded_environment_unary M false a f Hf IH).
Qed.

Corollary numerical_quotation_closed_environment M f b c n d e m k t v w :
  source_bounded M f (zeroM M) ->
  numerical_quotation M f b c n k t v -> numerical_quotation M f d e m k t w -> v=w.
Proof.
  intros Hb Hv Hw. apply (numerical_quotation_bounded_environment M f
    (zeroM M) b c n d e m k t v w Hb); [|exact Hv|exact Hw].
  intros i x y Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Print Assumptions bounded_environment_agreement_formula_correct.
Print Assumptions bounded_environment_agreement_cons.
Print Assumptions numerical_quotation_bounded_environment.
Print Assumptions numerical_quotation_closed_environment.



