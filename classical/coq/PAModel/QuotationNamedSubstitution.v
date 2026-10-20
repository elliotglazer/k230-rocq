(** Uniform commutation of quotation with named replacement of the total
    variable environment. All source codes, names, environment lengths and
    certificates may be nonstandard elements of the arithmetic model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula Pairing
  CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalEnvironments CodeTuples QuotationPayloads QuotationRules
  NumericalQuotation QuotationFunctionality NamedSubstitutionRules NamedSubstitution
  TemplateNamedSubstitution NumericalVacuity.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition environment_named_replace M b c n d e m x y :=
  forall i a a',environment_lookup M b c n i a -> environment_lookup M d e m i a' ->
    named_replace M x y a a'.
Definition environment_named_replace_formula (b c n d e m x y : term) : form :=
  ∀∀∀ (environment_lookup_formula b`[↑]`[↑]`[↑] c`[↑]`[↑]`[↑] n`[↑]`[↑]`[↑] $2 $1 →
    environment_lookup_formula d`[↑]`[↑]`[↑] e`[↑]`[↑]`[↑] m`[↑]`[↑]`[↑] $2 $0 →
    named_replace_formula x`[↑]`[↑]`[↑] y`[↑]`[↑]`[↑] $1 $0).
Local Opaque holds environment_lookup_formula named_replace_formula.
Lemma environment_named_replace_formula_correct M rho b c n d e m x y :
  holds M rho (environment_named_replace_formula b c n d e m x y) <->
  environment_named_replace M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m) (evalM M rho x) (evalM M rho y).
Proof.
  unfold environment_named_replace_formula,environment_named_replace.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite named_replace_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma environment_named_replace_cons M b c n d e m b' c' n' d' e' m' x y k :
  environment_named_replace M b c n d e m x y -> k<>x ->
  environment_cons M b c n k b' c' n' -> environment_cons M d e m k d' e' m' ->
  environment_named_replace M b' c' n' d' e' m' x y.
Proof.
  intros He Hkx Hc Hd i a a' Ha Ha'.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M b c n k b' c' n' a Hc)) in Ha.
    apply (proj1 (environment_cons_head M d e m k d' e' m' a' Hd)) in Ha'.
    subst a a'. right;auto.
  - apply (proj1 (environment_cons_tail M b c n k b' c' n' j a Hc)) in Ha.
    apply (proj1 (environment_cons_tail M d e m k d' e' m' j a' Hd)) in Ha'.
    exact (He j a a' Ha Ha').
Qed.

Lemma quotation_binary_named_substitution M h a b a' b' f g x y :
  x<>zeroM M -> named_substitution M a x y a' -> named_substitution M b x y b' ->
  quotation_binary M h a b f -> quotation_binary M h a' b' g ->
  named_substitution M f x y g.
Proof.
  intros Hx Ha Hb Hf Hg.
  assert (HA : expression_named_substitution M (a .: b .: fun _=>zeroM M)
    (a' .: b' .: fun _=>zeroM M) x y (CEvar 0) (CEvar 0)).
  { intros u u' -> ->. exact Ha. }
  assert (HB : expression_named_substitution M (a .: b .: fun _=>zeroM M)
    (a' .: b' .: fun _=>zeroM M) x y (CEvar 1) (CEvar 1)).
  { intros u u' -> ->. exact Hb. }
  destruct h; try exact (expression_ns_implication M _ _ x y _ _ _ _ HA HB f g Hf Hg).
  - exact (expression_ns_conjunction M _ _ x y _ _ _ _ Hx HA HB f g Hf Hg).
  - exact (expression_ns_disjunction M _ _ x y _ _ _ _ Hx HA HB f g Hf Hg).
Qed.

Lemma quotation_quantifier_named_substitution M universal k t a a' f g x y :
  x<>zeroM M -> t<>x -> k<>x -> k<>y ->
  named_substitution M a x y a' ->
  quotation_quantifier M universal k t a f -> quotation_quantifier M universal k t a' g ->
  named_substitution M f x y g.
Proof.
  intros Hx Htx Hkx Hky Ha Hf Hg.
  set (env:=k .: t .: a .: fun _=>zeroM M).
  set (env':=k .: t .: a' .: fun _=>zeroM M).
  assert (HA : expression_named_substitution M env env' x y (CEvar 2) (CEvar 2)).
  { intros u u' -> ->. exact Ha. }
  assert (HD : expression_named_substitution M env env' x y
      (E_wel (CEvar 1) (CEvar 0)) (E_wel (CEvar 1) (CEvar 0))).
  { apply (expression_ns_atom M env env' x y false).
    - intros u u' -> ->. right;auto.
    - intros u u' -> ->. right;auto. }
  destruct universal.
  - apply (expression_ns_universal M env env' x y (CEvar 0) (CEvar 0)
      (E_wim (E_wel (CEvar 1) (CEvar 0)) (CEvar 2))
      (E_wim (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)) k eq_refl eq_refl Hkx Hky);[|exact Hf|exact Hg].
    exact (expression_ns_implication M env env' x y _ _ _ _ HD HA).
  - apply (expression_ns_existential M env env' x y (CEvar 0) (CEvar 0)
      (E_wa (E_wel (CEvar 1) (CEvar 0)) (CEvar 2))
      (E_wa (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)) k Hx eq_refl eq_refl Hkx Hky);[|exact Hf|exact Hg].
    exact (expression_ns_conjunction M env env' x y _ _ _ _ Hx HD HA).
Qed.

Definition quotation_named_substitution_at M f :=
  forall b c n d e m k t x y v w,
    x<>zeroM M -> t<>x -> coding_lt M x k -> coding_lt M y k ->
    environment_named_replace M b c n d e m x y ->
    numerical_quotation M f b c n k t v -> numerical_quotation M f d e m k t w ->
    named_substitution M v x y w.
(** Twelve binders: b,c,n,d,e,m,k,t,x,y,v,w become slots 11..0. *)
Definition quotation_named_substitution_property : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀ ((¬ ($3 == zero)) → (¬ ($4 == $3)) →
    Peano.sless $3 $5 → Peano.sless $2 $5 →
    environment_named_replace_formula $11 $10 $9 $8 $7 $6 $3 $2 →
    numerical_quotation_formula $12 $11 $10 $9 $5 $4 $1 →
    numerical_quotation_formula $12 $8 $7 $6 $5 $4 $0 →
    named_substitution_formula $1 $3 $2 $0).
Local Opaque environment_named_replace_formula numerical_quotation_formula
  named_substitution_formula Peano.sless.
Lemma quotation_named_substitution_at_definable M :
  Definable1 M (quotation_named_substitution_at M).
Proof.
  exists quotation_named_substitution_property,(fun _=>zeroM M).
  intro f. unfold quotation_named_substitution_property,quotation_named_substitution_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct.
  setoid_rewrite environment_named_replace_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite named_substitution_formula_correct. reflexivity.
Qed.

Lemma quotation_named_substitution_invalid M f :
  (f=zeroM M \/ sf_invalid M f) -> quotation_named_substitution_at M f.
Proof.
  intros Hbad b c n d e m k t x y v w Hx Htx Hxl Hyl He Hv Hw.
  rewrite (numerical_quotation_invalid M f b c n k t v Hbad Hv),
    (numerical_quotation_invalid M f d e m k t w Hbad Hw).
  now apply named_substitution_one_fixed.
Qed.
Lemma quotation_named_substitution_atom M equality a q f :
  sf_relation M (quotation_source_atom equality) a q f -> quotation_named_substitution_at M f.
Proof.
  intros Hf b c n d e m k t x y v w Hx Htx Hxl Hyl He Hv Hw.
  destruct (numerical_quotation_atom_inv M equality a q f b c n k t v Hf Hv)
    as [u [z [Hu [Hz Hout]]]].
  destruct (numerical_quotation_atom_inv M equality a q f d e m k t w Hf Hw)
    as [u' [z' [Hu' [Hz' Hout']]]].
  exact (quotation_atom_named_substitution M equality u z u' z' t k x y v w
    Hx Htx Hxl Hyl (He a u u' Hu Hu') (He q z z' Hz Hz') Hout Hout').
Qed.
Lemma quotation_named_substitution_binary M h a q f :
  sf_binary h -> sf_relation M h a q f ->
  quotation_named_substitution_at M a -> quotation_named_substitution_at M q ->
  quotation_named_substitution_at M f.
Proof.
  intros Hh Hf IHa IHq b c n d e m k t x y v w Hx Htx Hxl Hyl He Hv Hw.
  destruct (numerical_quotation_binary_inv M h a q f b c n k t v Hh Hf Hv)
    as [u [z [Hu [Hz Hout]]]].
  destruct (numerical_quotation_binary_inv M h a q f d e m k t w Hh Hf Hw)
    as [u' [z' [Hu' [Hz' Hout']]]].
  exact (quotation_binary_named_substitution M h u z u' z' v w x y Hx
    (IHa b c n d e m k t x y u u' Hx Htx Hxl Hyl He Hu Hu')
    (IHq b c n d e m k t x y z z' Hx Htx Hxl Hyl He Hz Hz') Hout Hout').
Qed.
Lemma quotation_named_substitution_unary M universal a f :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  quotation_named_substitution_at M a -> quotation_named_substitution_at M f.
Proof.
  intros Hf IH b c n d e m k t x y v w Hx Htx Hxl Hyl He Hv Hw.
  destruct (numerical_quotation_unary_inv M universal a f b c n k t v Hf Hv)
    as [b' [c' [n' [u [Hcons [Hu Hout]]]]]].
  destruct (numerical_quotation_unary_inv M universal a f d e m k t w Hf Hw)
    as [d' [e' [m' [u' [Hcons' [Hu' Hout']]]]]].
  assert (Hkx : k<>x) by now apply template_lt_different.
  assert (Hky : k<>y) by now apply template_lt_different.
  exact (quotation_quantifier_named_substitution M universal k t u u' v w x y Hx Htx Hkx Hky
    (IH b' c' n' d' e' m' (succM M k) t x y u u' Hx Htx
      (coding_lt_trans M x k (succM M k) Hxl (coding_lt_succ M k))
      (coding_lt_trans M y k (succM M k) Hyl (coding_lt_succ M k))
      (environment_named_replace_cons M b c n d e m b' c' n' d' e' m' x y k He Hkx Hcons Hcons') Hu Hu')
    Hout Hout').
Qed.

Theorem numerical_quotation_named_substitution M f : quotation_named_substitution_at M f.
Proof.
  apply (sf_code_induction M (quotation_named_substitution_at M)).
  - apply quotation_named_substitution_at_definable.
  - apply quotation_named_substitution_invalid;now left.
  - intros f' H. apply quotation_named_substitution_invalid;now right.
  - intros a q f' H. exact (quotation_named_substitution_atom M false a q f' H).
  - intros a q f' H. exact (quotation_named_substitution_atom M true a q f' H).
  - exact (quotation_named_substitution_binary M).
  - intros h a f' [Hh|Hh] Hf IH;subst h.
    + exact (quotation_named_substitution_unary M true a f' Hf IH).
    + exact (quotation_named_substitution_unary M false a f' Hf IH).
Qed.

Corollary numerical_quotation_named_substitution_exists M f b c n d e m k t x y v :
  x<>zeroM M -> t<>x -> coding_lt M x k -> coding_lt M y k ->
  environment_named_replace M b c n d e m x y -> numerical_quotation M f b c n k t v ->
  exists w,numerical_quotation M f d e m k t w /\ named_substitution M v x y w.
Proof.
  intros Hx Htx Hxl Hyl He Hv.
  destruct (numerical_quotation_total M f d e m k t) as [w Hw].
  exists w. split;[exact Hw|].
  exact (numerical_quotation_named_substitution M f b c n d e m k t x y v w Hx Htx Hxl Hyl He Hv Hw).
Qed.

(** The binder-removal application: the source name is k, while both
    quotations start allocating local binders at its successor. *)
Corollary numerical_quotation_head_replacement M f b c n d e m k t y v w :
  coding_lt M t k -> coding_lt M y k ->
  environment_named_replace M b c n d e m k y ->
  numerical_quotation M f b c n (succM M k) t v ->
  numerical_quotation M f d e m (succM M k) t w ->
  named_substitution M v k y w.
Proof.
  intros Ht Hy He Hv Hw.
  apply (numerical_quotation_named_substitution M f b c n d e m (succM M k) t k y v w).
  - intro E. subst k. exact (coding_not_lt_zero M y Hy).
  - intro E. apply (template_lt_different M t k Ht). symmetry. exact E.
  - apply coding_lt_succ.
  - exact (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k)).
  - exact He.
  - exact Hv.
  - exact Hw.
Qed.
