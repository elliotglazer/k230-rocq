(** Uniqueness of internally certified source quotation, including across
    different beta codes and lengths representing the same environment. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalEnvironmentExt CodeTuples QuotationPayloads
  NumericalTraces QuotationRules NumericalQuotation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem numerical_quotation_cases M f b c n k t v :
  numerical_quotation M f b c n k t v ->
  quotation_leaf M f b c n k t v \/
  (exists universal a d e m w,
    sf_relation M (quotation_source_quantifier universal) a (zeroM M) f /\
    environment_cons M b c n k d e m /\
    numerical_quotation M a d e m (succM M k) t w /\
    quotation_quantifier M universal k t w v) \/
  (exists h a d x y,
    sf_binary h /\ sf_relation M h a d f /\
    numerical_quotation M a b c n k t x /\
    numerical_quotation M d b c n k t y /\ quotation_binary M h x y v).
Proof.
  intros [r [Hr Htrace]].
  destruct (trace_derives_inv M quotation_rules r Htrace)
    as [Hb|[[p [Hp Hu]]|[p [q [Hp [Hq Hbin]]]]]].
  - apply quotation_rule_base in Hb.
    destruct Hb as [f' [b' [c' [n' [k' [t' [v' [Hr' Hleaf]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. now left.
  - apply quotation_rule_unary in Hu.
    destruct Hu as [f' [b' [c' [n' [k' [t' [v' [Hr' Hcase]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. right; left.
    destruct Hcase as [Hcase|Hcase];
      destruct Hcase as [a [d [e [m [w [Hpw [He [Hf Hv]]]]]]]].
    + exists true,a,d,e,m,w. split; [exact Hf|]. split; [exact He|]. split; [exists p;auto|exact Hv].
    + exists false,a,d,e,m,w. split; [exact Hf|]. split; [exact He|]. split; [exists p;auto|exact Hv].
  - apply quotation_rule_binary in Hbin.
    destruct Hbin as [f' [b' [c' [n' [k' [t' [v' [Hr' Hcase]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. right; right.
    destruct Hcase as [Hcase|[Hcase|Hcase]];
      destruct Hcase as [a [d [x [y [Hpx [Hqy [Hf Hv]]]]]]].
    + exists SFAnd,a,d,x,y. split; [now left|]. split; [exact Hf|].
      split; [exists p;auto|]. split; [exists q;auto|exact Hv].
    + exists SFOr,a,d,x,y. split; [right;now left|]. split; [exact Hf|].
      split; [exists p;auto|]. split; [exists q;auto|exact Hv].
    + exists SFImpl,a,d,x,y. split; [right;now right|]. split; [exact Hf|].
      split; [exists p;auto|]. split; [exists q;auto|exact Hv].
Qed.

Lemma quotation_invalid_relation M f h a d :
  (f=zeroM M \/ sf_invalid M f) -> sf_relation M h a d f -> False.
Proof.
  intros [E|Hbad] Hf.
  - exact (sf_relation_nonzero M h a d f Hf E).
  - exact (sf_invalid_not_constructor M h a d f Hbad Hf).
Qed.

Lemma numerical_quotation_invalid M f b c n k t v :
  (f=zeroM M \/ sf_invalid M f) -> numerical_quotation M f b c n k t v ->
  v=code_numeral M 1.
Proof.
  intros Hbad H. apply numerical_quotation_cases in H.
  destruct H as [[[Hbad' Hv]|[Ha|Ha]]|[Hu|Hb]]; [exact Hv| | | |].
  - destruct Ha as [a [d [x [y [Hf _]]]]].
    exfalso. eapply quotation_invalid_relation; eassumption.
  - destruct Ha as [a [d [x [y [Hf _]]]]].
    exfalso. eapply quotation_invalid_relation; eassumption.
  - destruct Hu as [universal [a [d [e [m [w [Hf _]]]]]]].
    exfalso. eapply quotation_invalid_relation; eassumption.
  - destruct Hb as [h [a [d [x [y [_ [Hf _]]]]]]].
    exfalso. eapply quotation_invalid_relation; eassumption.
Qed.

Lemma quotation_source_atom_injective x y :
  quotation_source_atom x=quotation_source_atom y -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.
Lemma quotation_source_quantifier_injective x y :
  quotation_source_quantifier x=quotation_source_quantifier y -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.
Lemma quotation_atom_quantifier_distinct x y :
  quotation_source_atom x<>quotation_source_quantifier y.
Proof. destruct x,y; discriminate. Qed.
Lemma quotation_atom_binary_distinct x h : sf_binary h -> quotation_source_atom x<>h.
Proof. intros [H|[H|H]]; subst h; destruct x; discriminate. Qed.
Lemma quotation_quantifier_binary_distinct x h : sf_binary h -> quotation_source_quantifier x<>h.
Proof. intros [H|[H|H]]; subst h; destruct x; discriminate. Qed.
Lemma quotation_atom_second M x d : sf_payload_second M (quotation_source_atom x) d=d.
Proof. destruct x; reflexivity. Qed.
Lemma quotation_binary_second M h d : sf_binary h -> sf_payload_second M h d=d.
Proof. intros [H|[H|H]]; subst h; reflexivity. Qed.

Lemma numerical_quotation_atom_inv M equality a d f b c n k t v :
  sf_relation M (quotation_source_atom equality) a d f ->
  numerical_quotation M f b c n k t v ->
  exists x y, environment_lookup M b c n a x /\
    environment_lookup M b c n d y /\ quotation_atom M equality x y t k v.
Proof.
  intros Hf H. apply numerical_quotation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply quotation_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' [Hx [Hy Hv]]]]]]].
    destruct (sf_relation_injective M (quotation_source_atom equality)
      (quotation_source_atom false) a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    apply quotation_source_atom_injective in Eh. subst equality a'.
    cbn [quotation_source_atom sf_payload_second] in Ed. subst d'. exists x,y. auto.
  - destruct Ha as [a' [d' [x [y [Hf' [Hx [Hy Hv]]]]]]].
    destruct (sf_relation_injective M (quotation_source_atom equality)
      (quotation_source_atom true) a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    apply quotation_source_atom_injective in Eh. subst equality a'.
    cbn [quotation_source_atom sf_payload_second] in Ed. subst d'. exists x,y. auto.
  - destruct Hu as [universal [a' [d' [e [m [w [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (quotation_atom_quantifier_distinct equality universal Eh).
  - destruct Hb as [h [a' [d' [x [y [Hh [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (quotation_atom_binary_distinct equality h Hh Eh).
Qed.

Lemma numerical_quotation_binary_inv M h a d f b c n k t v :
  sf_binary h -> sf_relation M h a d f -> numerical_quotation M f b c n k t v ->
  exists x y, numerical_quotation M a b c n k t x /\
    numerical_quotation M d b c n k t y /\ quotation_binary M h x y v.
Proof.
  intros Hh Hf H. apply numerical_quotation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply quotation_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (quotation_atom_binary_distinct false h Hh Eh).
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (quotation_atom_binary_distinct true h Hh Eh).
  - destruct Hu as [universal [a' [d' [e [m [w [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (quotation_quantifier_binary_distinct universal h Hh Eh).
  - destruct Hb as [h' [a' [d' [x [y [Hh' [Hf' [Hx [Hy Hv]]]]]]]]].
    destruct (sf_relation_injective M h h' a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    subst h' a'. rewrite !quotation_binary_second in Ed by exact Hh. subst d'.
    exists x,y. auto.
Qed.

Lemma numerical_quotation_unary_inv M universal a f b c n k t v :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  numerical_quotation M f b c n k t v ->
  exists d e m w, environment_cons M b c n k d e m /\
    numerical_quotation M a d e m (succM M k) t w /\
    quotation_quantifier M universal k t w v.
Proof.
  intros Hf H. apply numerical_quotation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply quotation_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (quotation_atom_quantifier_distinct false universal Eh).
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (quotation_atom_quantifier_distinct true universal Eh).
  - destruct Hu as [universal' [a' [d' [e [m [w [Hf' [He [Hw Hv]]]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh [Ea _]].
    apply quotation_source_quantifier_injective in Eh. subst universal' a'.
    exists d',e,m,w. auto.
  - destruct Hb as [h [a' [d' [x [y [Hh [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (quotation_quantifier_binary_distinct universal h Hh Eh).
Qed.

Definition quotation_functional_at M f : Prop :=
  forall b c n d e m k t v w,
    environment_equivalent M b c n d e m ->
    numerical_quotation M f b c n k t v ->
    numerical_quotation M f d e m k t w -> v=w.

(** After ten binders, slots 9..0 are b,c,n,d,e,m,k,t,v,w; source f is 10. *)
Definition quotation_functionality_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀ (environment_equivalent_formula $9 $8 $7 $6 $5 $4 →
    numerical_quotation_formula $10 $9 $8 $7 $3 $2 $1 →
    numerical_quotation_formula $10 $6 $5 $4 $3 $2 $0 → $1 == $0).

Local Opaque holds environment_equivalent_formula numerical_quotation_formula.
Lemma quotation_functional_at_definable M : Definable1 M (quotation_functional_at M).
Proof.
  exists quotation_functionality_formula,(fun _ => zeroM M).
  intro f. unfold quotation_functionality_formula,quotation_functional_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite environment_equivalent_formula_correct.
  setoid_rewrite numerical_quotation_formula_correct. reflexivity.
Qed.

Lemma quotation_functional_atom M equality a d f :
  sf_relation M (quotation_source_atom equality) a d f -> quotation_functional_at M f.
Proof.
  intros Hf b c n b' c' n' k t v w Heq Hv Hw.
  destruct (numerical_quotation_atom_inv M equality a d f b c n k t v Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (numerical_quotation_atom_inv M equality a d f b' c' n' k t w Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (environment_equivalent_lookup_determinacy M b c n b' c' n' a x x' Heq Hx Hx').
  assert (Ey : y=y') by exact (environment_equivalent_lookup_determinacy M b c n b' c' n' d y y' Heq Hy Hy').
  subst x' y'. exact (quotation_atom_functional M equality x y t k v w Hout Hout').
Qed.

Lemma quotation_functional_binary M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  quotation_functional_at M a -> quotation_functional_at M d -> quotation_functional_at M f.
Proof.
  intros Hh Hf IHa IHd b c n b' c' n' k t v w Heq Hv Hw.
  destruct (numerical_quotation_binary_inv M h a d f b c n k t v Hh Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (numerical_quotation_binary_inv M h a d f b' c' n' k t w Hh Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (IHa b c n b' c' n' k t x x' Heq Hx Hx').
  assert (Ey : y=y') by exact (IHd b c n b' c' n' k t y y' Heq Hy Hy').
  subst x' y'. exact (quotation_binary_functional M h x y v w Hout Hout').
Qed.

Lemma quotation_functional_unary M universal a f :
  sf_relation M (quotation_source_quantifier universal) a (zeroM M) f ->
  quotation_functional_at M a -> quotation_functional_at M f.
Proof.
  intros Hf IH b c n b' c' n' k t v w Heq Hv Hw.
  destruct (numerical_quotation_unary_inv M universal a f b c n k t v Hf Hv)
    as [d [e [m [x [Hcons [Hx Hout]]]]]].
  destruct (numerical_quotation_unary_inv M universal a f b' c' n' k t w Hf Hw)
    as [d' [e' [m' [y [Hcons' [Hy Hout']]]]]].
  assert (Hchild : environment_equivalent M d e m d' e' m').
  { exact (environment_cons_extensional M b c n b' c' n' k d e m d' e' m' Heq Hcons Hcons'). }
  assert (Ex : x=y) by exact (IH d e m d' e' m' (succM M k) t x y Hchild Hx Hy).
  subst y. exact (quotation_quantifier_functional M universal k t x v w Hout Hout').
Qed.

Theorem numerical_quotation_functional_equivalent M f : quotation_functional_at M f.
Proof.
  revert f. apply (sf_code_induction M (quotation_functional_at M)).
  - apply quotation_functional_at_definable.
  - intros b c n d e m k t v w Heq Hv Hw.
    rewrite (numerical_quotation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) Hv),
      (numerical_quotation_invalid M (zeroM M) d e m k t w (or_introl eq_refl) Hw). reflexivity.
  - intros f Hbad b c n d e m k t v w Heq Hv Hw.
    rewrite (numerical_quotation_invalid M f b c n k t v (or_intror Hbad) Hv),
      (numerical_quotation_invalid M f d e m k t w (or_intror Hbad) Hw). reflexivity.
  - intros a d f Hf. exact (quotation_functional_atom M false a d f Hf).
  - intros a d f Hf. exact (quotation_functional_atom M true a d f Hf).
  - exact (quotation_functional_binary M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (quotation_functional_unary M true a f Hf IH).
    + exact (quotation_functional_unary M false a f Hf IH).
Qed.

Corollary numerical_quotation_functional M f b c n k t v w :
  numerical_quotation M f b c n k t v -> numerical_quotation M f b c n k t w -> v=w.
Proof.
  apply (numerical_quotation_functional_equivalent M f b c n b c n k t v w).
  apply environment_equivalent_refl.
Qed.

Corollary numerical_quotation_environment_extensional M f b c n d e m k t v :
  environment_equivalent M b c n d e m ->
  (numerical_quotation M f b c n k t v <-> numerical_quotation M f d e m k t v).
Proof.
  intro Heq. split; intro Hv.
  - destruct (numerical_quotation_total M f d e m k t) as [w Hw].
    assert (E : v=w) by exact (numerical_quotation_functional_equivalent M f b c n d e m k t v w Heq Hv Hw).
    now subst w.
  - destruct (numerical_quotation_total M f b c n k t) as [w Hw].
    assert (E : w=v) by exact (numerical_quotation_functional_equivalent M f b c n d e m k t w v Heq Hw Hv).
    now subst w.
Qed.
