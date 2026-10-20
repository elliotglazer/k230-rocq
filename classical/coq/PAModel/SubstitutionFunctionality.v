(** Uniqueness of numerical substitution across extensionally equal prefix maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalSubstitutionMaps NumericalEnvironmentExt CodeTuples SubstitutionPayloads
  NumericalTraces SubstitutionRules SubstitutionComputation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem substitution_computation_cases M f b c n k t v :
  substitution_computation M f b c n k t v ->
  substitution_leaf M f b c n k t v \/
  (exists universal a d e m w,
    sf_relation M (substitution_source_quantifier universal) a (zeroM M) f /\
    substitution_lift M b c n k d e m /\
    substitution_computation M a d e m (succM M k) t w /\
    substitution_quantifier M universal k t w v) \/
  (exists h a d x y,
    sf_binary h /\ sf_relation M h a d f /\
    substitution_computation M a b c n k t x /\
    substitution_computation M d b c n k t y /\ substitution_binary M h x y v).
Proof.
  intros [r [Hr Htrace]].
  destruct (trace_derives_inv M substitution_rules r Htrace)
    as [Hb|[[p [Hp Hu]]|[p [q [Hp [Hq Hbin]]]]]].
  - apply substitution_rule_base in Hb.
    destruct Hb as [f' [b' [c' [n' [k' [t' [v' [Hr' Hleaf]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. now left.
  - apply substitution_rule_unary in Hu.
    destruct Hu as [f' [b' [c' [n' [k' [t' [v' [Hr' Hcase]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. right; left.
    destruct Hcase as [Hcase|Hcase];
      destruct Hcase as [a [d [e [m [w [Hpw [He [Hf Hv]]]]]]]].
    + exists true,a,d,e,m,w. split; [exact Hf|]. split; [exact He|]. split; [exists p;auto|exact Hv].
    + exists false,a,d,e,m,w. split; [exact Hf|]. split; [exact He|]. split; [exists p;auto|exact Hv].
  - apply substitution_rule_binary in Hbin.
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

Lemma substitution_invalid_relation M f h a d :
  (f=zeroM M \/ sf_invalid M f) -> sf_relation M h a d f -> False.
Proof.
  intros [E|Hbad] Hf.
  - exact (sf_relation_nonzero M h a d f Hf E).
  - exact (sf_invalid_not_constructor M h a d f Hbad Hf).
Qed.

Lemma substitution_computation_invalid M f b c n k t v :
  (f=zeroM M \/ sf_invalid M f) -> substitution_computation M f b c n k t v ->
  v=zeroM M.
Proof.
  intros Hbad H. apply substitution_computation_cases in H.
  destruct H as [[[Hbad' Hv]|[Ha|Ha]]|[Hu|Hb]]; [exact Hv| | | |].
  - destruct Ha as [a [d [x [y [Hf _]]]]].
    exfalso. eapply substitution_invalid_relation; eassumption.
  - destruct Ha as [a [d [x [y [Hf _]]]]].
    exfalso. eapply substitution_invalid_relation; eassumption.
  - destruct Hu as [universal [a [d [e [m [w [Hf _]]]]]]].
    exfalso. eapply substitution_invalid_relation; eassumption.
  - destruct Hb as [h [a [d [x [y [_ [Hf _]]]]]]].
    exfalso. eapply substitution_invalid_relation; eassumption.
Qed.

Lemma substitution_source_atom_injective x y :
  substitution_source_atom x=substitution_source_atom y -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.
Lemma substitution_source_quantifier_injective x y :
  substitution_source_quantifier x=substitution_source_quantifier y -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.
Lemma substitution_atom_quantifier_distinct x y :
  substitution_source_atom x<>substitution_source_quantifier y.
Proof. destruct x,y; discriminate. Qed.
Lemma substitution_atom_binary_distinct x h : sf_binary h -> substitution_source_atom x<>h.
Proof. intros [H|[H|H]]; subst h; destruct x; discriminate. Qed.
Lemma substitution_quantifier_binary_distinct x h : sf_binary h -> substitution_source_quantifier x<>h.
Proof. intros [H|[H|H]]; subst h; destruct x; discriminate. Qed.
Lemma substitution_atom_second M x d : sf_payload_second M (substitution_source_atom x) d=d.
Proof. destruct x; reflexivity. Qed.
Lemma substitution_binary_second M h d : sf_binary h -> sf_payload_second M h d=d.
Proof. intros [H|[H|H]]; subst h; reflexivity. Qed.

Lemma substitution_computation_atom_inv M equality a d f b c n k t v :
  sf_relation M (substitution_source_atom equality) a d f ->
  substitution_computation M f b c n k t v ->
  exists x y, substitution_lookup M b c n k a x /\
    substitution_lookup M b c n k d y /\ substitution_atom M equality x y t k v.
Proof.
  intros Hf H. apply substitution_computation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply substitution_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' [Hx [Hy Hv]]]]]]].
    destruct (sf_relation_injective M (substitution_source_atom equality)
      (substitution_source_atom false) a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    apply substitution_source_atom_injective in Eh. subst equality a'.
    cbn [substitution_source_atom sf_payload_second] in Ed. subst d'. exists x,y. auto.
  - destruct Ha as [a' [d' [x [y [Hf' [Hx [Hy Hv]]]]]]].
    destruct (sf_relation_injective M (substitution_source_atom equality)
      (substitution_source_atom true) a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    apply substitution_source_atom_injective in Eh. subst equality a'.
    cbn [substitution_source_atom sf_payload_second] in Ed. subst d'. exists x,y. auto.
  - destruct Hu as [universal [a' [d' [e [m [w [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (substitution_atom_quantifier_distinct equality universal Eh).
  - destruct Hb as [h [a' [d' [x [y [Hh [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (substitution_atom_binary_distinct equality h Hh Eh).
Qed.

Lemma substitution_computation_binary_inv M h a d f b c n k t v :
  sf_binary h -> sf_relation M h a d f -> substitution_computation M f b c n k t v ->
  exists x y, substitution_computation M a b c n k t x /\
    substitution_computation M d b c n k t y /\ substitution_binary M h x y v.
Proof.
  intros Hh Hf H. apply substitution_computation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply substitution_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (substitution_atom_binary_distinct false h Hh Eh).
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (substitution_atom_binary_distinct true h Hh Eh).
  - destruct Hu as [universal [a' [d' [e [m [w [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (substitution_quantifier_binary_distinct universal h Hh Eh).
  - destruct Hb as [h' [a' [d' [x [y [Hh' [Hf' [Hx [Hy Hv]]]]]]]]].
    destruct (sf_relation_injective M h h' a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    subst h' a'. rewrite !substitution_binary_second in Ed by exact Hh. subst d'.
    exists x,y. auto.
Qed.

Lemma substitution_computation_unary_inv M universal a f b c n k t v :
  sf_relation M (substitution_source_quantifier universal) a (zeroM M) f ->
  substitution_computation M f b c n k t v ->
  exists d e m w, substitution_lift M b c n k d e m /\
    substitution_computation M a d e m (succM M k) t w /\
    substitution_quantifier M universal k t w v.
Proof.
  intros Hf H. apply substitution_computation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply substitution_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (substitution_atom_quantifier_distinct false universal Eh).
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (substitution_atom_quantifier_distinct true universal Eh).
  - destruct Hu as [universal' [a' [d' [e [m [w [Hf' [He [Hw Hv]]]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh [Ea _]].
    apply substitution_source_quantifier_injective in Eh. subst universal' a'.
    exists d',e,m,w. auto.
  - destruct Hb as [h [a' [d' [x [y [Hh [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (substitution_quantifier_binary_distinct universal h Hh Eh).
Qed.

Definition substitution_functional_at M f : Prop :=
  forall b c n d e m k t v w,
    substitution_equivalent M b c n d e m k ->
    substitution_computation M f b c n k t v ->
    substitution_computation M f d e m k t w -> v=w.

(** After ten binders, slots 9..0 are b,c,n,d,e,m,k,t,v,w; source f is 10. *)
Definition substitution_functionality_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀ (substitution_equivalent_formula $9 $8 $7 $6 $5 $4 $3 →
    substitution_computation_formula $10 $9 $8 $7 $3 $2 $1 →
    substitution_computation_formula $10 $6 $5 $4 $3 $2 $0 → $1 == $0).

Local Opaque holds substitution_equivalent_formula substitution_computation_formula.
Lemma substitution_functional_at_definable M : Definable1 M (substitution_functional_at M).
Proof.
  exists substitution_functionality_formula,(fun _ => zeroM M).
  intro f. unfold substitution_functionality_formula,substitution_functional_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite substitution_equivalent_formula_correct.
  setoid_rewrite substitution_computation_formula_correct. reflexivity.
Qed.

Lemma substitution_functional_atom M equality a d f :
  sf_relation M (substitution_source_atom equality) a d f -> substitution_functional_at M f.
Proof.
  intros Hf b c n b' c' n' k t v w Heq Hv Hw.
  destruct (substitution_computation_atom_inv M equality a d f b c n k t v Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (substitution_computation_atom_inv M equality a d f b' c' n' k t w Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (substitution_equivalent_lookup_determinacy M b c n b' c' n' k a x x' Heq Hx Hx').
  assert (Ey : y=y') by exact (substitution_equivalent_lookup_determinacy M b c n b' c' n' k d y y' Heq Hy Hy').
  subst x' y'. exact (substitution_atom_functional M equality x y t k v w Hout Hout').
Qed.

Lemma substitution_functional_binary M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  substitution_functional_at M a -> substitution_functional_at M d -> substitution_functional_at M f.
Proof.
  intros Hh Hf IHa IHd b c n b' c' n' k t v w Heq Hv Hw.
  destruct (substitution_computation_binary_inv M h a d f b c n k t v Hh Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (substitution_computation_binary_inv M h a d f b' c' n' k t w Hh Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (IHa b c n b' c' n' k t x x' Heq Hx Hx').
  assert (Ey : y=y') by exact (IHd b c n b' c' n' k t y y' Heq Hy Hy').
  subst x' y'. exact (substitution_binary_functional M h x y v w Hout Hout').
Qed.

Lemma substitution_functional_unary M universal a f :
  sf_relation M (substitution_source_quantifier universal) a (zeroM M) f ->
  substitution_functional_at M a -> substitution_functional_at M f.
Proof.
  intros Hf IH b c n b' c' n' k t v w Heq Hv Hw.
  destruct (substitution_computation_unary_inv M universal a f b c n k t v Hf Hv)
    as [d [e [m [x [Hcons [Hx Hout]]]]]].
  destruct (substitution_computation_unary_inv M universal a f b' c' n' k t w Hf Hw)
    as [d' [e' [m' [y [Hcons' [Hy Hout']]]]]].
  assert (Hchild : substitution_equivalent M d e m d' e' m' (succM M k)).
  { exact (substitution_lift_extensional M b c n b' c' n' k d e m d' e' m' Heq Hcons Hcons'). }
  assert (Ex : x=y) by exact (IH d e m d' e' m' (succM M k) t x y Hchild Hx Hy).
  subst y. exact (substitution_quantifier_functional M universal k t x v w Hout Hout').
Qed.

Theorem substitution_computation_functional_equivalent M f : substitution_functional_at M f.
Proof.
  revert f. apply (sf_code_induction M (substitution_functional_at M)).
  - apply substitution_functional_at_definable.
  - intros b c n d e m k t v w Heq Hv Hw.
    rewrite (substitution_computation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) Hv),
      (substitution_computation_invalid M (zeroM M) d e m k t w (or_introl eq_refl) Hw). reflexivity.
  - intros f Hbad b c n d e m k t v w Heq Hv Hw.
    rewrite (substitution_computation_invalid M f b c n k t v (or_intror Hbad) Hv),
      (substitution_computation_invalid M f d e m k t w (or_intror Hbad) Hw). reflexivity.
  - intros a d f Hf. exact (substitution_functional_atom M false a d f Hf).
  - intros a d f Hf. exact (substitution_functional_atom M true a d f Hf).
  - exact (substitution_functional_binary M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (substitution_functional_unary M true a f Hf IH).
    + exact (substitution_functional_unary M false a f Hf IH).
Qed.

Corollary substitution_computation_functional M f b c n k t v w :
  substitution_computation M f b c n k t v -> substitution_computation M f b c n k t w -> v=w.
Proof.
  apply (substitution_computation_functional_equivalent M f b c n b c n k t v w).
  apply substitution_equivalent_refl.
Qed.

Corollary substitution_computation_environment_extensional M f b c n d e m k t v :
  substitution_equivalent M b c n d e m k ->
  (substitution_computation M f b c n k t v <-> substitution_computation M f d e m k t v).
Proof.
  intro Heq. split; intro Hv.
  - destruct (substitution_computation_total M f d e m k t) as [w Hw].
    assert (E : v=w) by exact (substitution_computation_functional_equivalent M f b c n d e m k t v w Heq Hv Hw).
    now subst w.
  - destruct (substitution_computation_total M f b c n k t) as [w Hw].
    assert (E : w=v) by exact (substitution_computation_functional_equivalent M f b c n d e m k t w v Heq Hw Hv).
    now subst w.
Qed.
