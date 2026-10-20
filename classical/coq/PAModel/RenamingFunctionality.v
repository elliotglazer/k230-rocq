(** Uniqueness of numerical renaming across extensionally equal prefix maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalRenamingMaps NumericalEnvironmentExt CodeTuples RenamingPayloads
  NumericalTraces RenamingRules RenamingComputation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem renaming_computation_cases M f b c n k t v :
  renaming_computation M f b c n k t v ->
  renaming_leaf M f b c n k t v \/
  (exists universal a d e m w,
    sf_relation M (renaming_source_quantifier universal) a (zeroM M) f /\
    renaming_lift M b c n k d e m /\
    renaming_computation M a d e m k t w /\
    renaming_quantifier M universal k t w v) \/
  (exists h a d x y,
    sf_binary h /\ sf_relation M h a d f /\
    renaming_computation M a b c n k t x /\
    renaming_computation M d b c n k t y /\ renaming_binary M h x y v).
Proof.
  intros [r [Hr Htrace]].
  destruct (trace_derives_inv M renaming_rules r Htrace)
    as [Hb|[[p [Hp Hu]]|[p [q [Hp [Hq Hbin]]]]]].
  - apply renaming_rule_base in Hb.
    destruct Hb as [f' [b' [c' [n' [k' [t' [v' [Hr' Hleaf]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. now left.
  - apply renaming_rule_unary in Hu.
    destruct Hu as [f' [b' [c' [n' [k' [t' [v' [Hr' Hcase]]]]]]]].
    destruct (tuple7_injective M f b c n k t v f' b' c' n' k' t' v' r Hr Hr')
      as [Ef [Eb [Ec [En [Ek [Et Ev]]]]]].
    subst f' b' c' n' k' t' v'. right; left.
    destruct Hcase as [Hcase|Hcase];
      destruct Hcase as [a [d [e [m [w [Hpw [He [Hf Hv]]]]]]]].
    + exists true,a,d,e,m,w. split; [exact Hf|]. split; [exact He|]. split; [exists p;auto|exact Hv].
    + exists false,a,d,e,m,w. split; [exact Hf|]. split; [exact He|]. split; [exists p;auto|exact Hv].
  - apply renaming_rule_binary in Hbin.
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

Lemma renaming_invalid_relation M f h a d :
  (f=zeroM M \/ sf_invalid M f) -> sf_relation M h a d f -> False.
Proof.
  intros [E|Hbad] Hf.
  - exact (sf_relation_nonzero M h a d f Hf E).
  - exact (sf_invalid_not_constructor M h a d f Hbad Hf).
Qed.

Lemma renaming_computation_invalid M f b c n k t v :
  (f=zeroM M \/ sf_invalid M f) -> renaming_computation M f b c n k t v ->
  v=zeroM M.
Proof.
  intros Hbad H. apply renaming_computation_cases in H.
  destruct H as [[[Hbad' Hv]|[Ha|Ha]]|[Hu|Hb]]; [exact Hv| | | |].
  - destruct Ha as [a [d [x [y [Hf _]]]]].
    exfalso. eapply renaming_invalid_relation; eassumption.
  - destruct Ha as [a [d [x [y [Hf _]]]]].
    exfalso. eapply renaming_invalid_relation; eassumption.
  - destruct Hu as [universal [a [d [e [m [w [Hf _]]]]]]].
    exfalso. eapply renaming_invalid_relation; eassumption.
  - destruct Hb as [h [a [d [x [y [_ [Hf _]]]]]]].
    exfalso. eapply renaming_invalid_relation; eassumption.
Qed.

Lemma renaming_source_atom_injective x y :
  renaming_source_atom x=renaming_source_atom y -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.
Lemma renaming_source_quantifier_injective x y :
  renaming_source_quantifier x=renaming_source_quantifier y -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.
Lemma renaming_atom_quantifier_distinct x y :
  renaming_source_atom x<>renaming_source_quantifier y.
Proof. destruct x,y; discriminate. Qed.
Lemma renaming_atom_binary_distinct x h : sf_binary h -> renaming_source_atom x<>h.
Proof. intros [H|[H|H]]; subst h; destruct x; discriminate. Qed.
Lemma renaming_quantifier_binary_distinct x h : sf_binary h -> renaming_source_quantifier x<>h.
Proof. intros [H|[H|H]]; subst h; destruct x; discriminate. Qed.
Lemma renaming_atom_second M x d : sf_payload_second M (renaming_source_atom x) d=d.
Proof. destruct x; reflexivity. Qed.
Lemma renaming_binary_second M h d : sf_binary h -> sf_payload_second M h d=d.
Proof. intros [H|[H|H]]; subst h; reflexivity. Qed.

Lemma renaming_computation_atom_inv M equality a d f b c n k t v :
  sf_relation M (renaming_source_atom equality) a d f ->
  renaming_computation M f b c n k t v ->
  exists x y, renaming_lookup M b c n k a x /\
    renaming_lookup M b c n k d y /\ renaming_atom M equality x y t k v.
Proof.
  intros Hf H. apply renaming_computation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply renaming_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' [Hx [Hy Hv]]]]]]].
    destruct (sf_relation_injective M (renaming_source_atom equality)
      (renaming_source_atom false) a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    apply renaming_source_atom_injective in Eh. subst equality a'.
    cbn [renaming_source_atom sf_payload_second] in Ed. subst d'. exists x,y. auto.
  - destruct Ha as [a' [d' [x [y [Hf' [Hx [Hy Hv]]]]]]].
    destruct (sf_relation_injective M (renaming_source_atom equality)
      (renaming_source_atom true) a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    apply renaming_source_atom_injective in Eh. subst equality a'.
    cbn [renaming_source_atom sf_payload_second] in Ed. subst d'. exists x,y. auto.
  - destruct Hu as [universal [a' [d' [e [m [w [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (renaming_atom_quantifier_distinct equality universal Eh).
  - destruct Hb as [h [a' [d' [x [y [Hh [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (renaming_atom_binary_distinct equality h Hh Eh).
Qed.

Lemma renaming_computation_binary_inv M h a d f b c n k t v :
  sf_binary h -> sf_relation M h a d f -> renaming_computation M f b c n k t v ->
  exists x y, renaming_computation M a b c n k t x /\
    renaming_computation M d b c n k t y /\ renaming_binary M h x y v.
Proof.
  intros Hh Hf H. apply renaming_computation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply renaming_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (renaming_atom_binary_distinct false h Hh Eh).
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (renaming_atom_binary_distinct true h Hh Eh).
  - destruct Hu as [universal [a' [d' [e [m [w [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (renaming_quantifier_binary_distinct universal h Hh Eh).
  - destruct Hb as [h' [a' [d' [x [y [Hh' [Hf' [Hx [Hy Hv]]]]]]]]].
    destruct (sf_relation_injective M h h' a d a' d' f Hf Hf') as [Eh [Ea Ed]].
    subst h' a'. rewrite !renaming_binary_second in Ed by exact Hh. subst d'.
    exists x,y. auto.
Qed.

Lemma renaming_computation_unary_inv M universal a f b c n k t v :
  sf_relation M (renaming_source_quantifier universal) a (zeroM M) f ->
  renaming_computation M f b c n k t v ->
  exists d e m w, renaming_lift M b c n k d e m /\
    renaming_computation M a d e m k t w /\
    renaming_quantifier M universal k t w v.
Proof.
  intros Hf H. apply renaming_computation_cases in H.
  destruct H as [[[Hbad Hv]|[Ha|Ha]]|[Hu|Hb]].
  - exfalso. eapply renaming_invalid_relation; eassumption.
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (renaming_atom_quantifier_distinct false universal Eh).
  - destruct Ha as [a' [d' [x [y [Hf' _]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf' Hf) as [Eh _].
    exfalso. exact (renaming_atom_quantifier_distinct true universal Eh).
  - destruct Hu as [universal' [a' [d' [e [m [w [Hf' [He [Hw Hv]]]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh [Ea _]].
    apply renaming_source_quantifier_injective in Eh. subst universal' a'.
    exists d',e,m,w. auto.
  - destruct Hb as [h [a' [d' [x [y [Hh [Hf' _]]]]]]].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    exfalso. exact (renaming_quantifier_binary_distinct universal h Hh Eh).
Qed.

Definition renaming_functional_at M f : Prop :=
  forall b c n d e m k t v w,
    renaming_equivalent M b c n d e m k ->
    renaming_computation M f b c n k t v ->
    renaming_computation M f d e m k t w -> v=w.

(** After ten binders, slots 9..0 are b,c,n,d,e,m,k,t,v,w; source f is 10. *)
Definition renaming_functionality_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀ (renaming_equivalent_formula $9 $8 $7 $6 $5 $4 $3 →
    renaming_computation_formula $10 $9 $8 $7 $3 $2 $1 →
    renaming_computation_formula $10 $6 $5 $4 $3 $2 $0 → $1 == $0).

Local Opaque holds renaming_equivalent_formula renaming_computation_formula.
Lemma renaming_functional_at_definable M : Definable1 M (renaming_functional_at M).
Proof.
  exists renaming_functionality_formula,(fun _ => zeroM M).
  intro f. unfold renaming_functionality_formula,renaming_functional_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite renaming_equivalent_formula_correct.
  setoid_rewrite renaming_computation_formula_correct. reflexivity.
Qed.

Lemma renaming_functional_atom M equality a d f :
  sf_relation M (renaming_source_atom equality) a d f -> renaming_functional_at M f.
Proof.
  intros Hf b c n b' c' n' k t v w Heq Hv Hw.
  destruct (renaming_computation_atom_inv M equality a d f b c n k t v Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (renaming_computation_atom_inv M equality a d f b' c' n' k t w Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (renaming_equivalent_lookup_determinacy M b c n b' c' n' k a x x' Heq Hx Hx').
  assert (Ey : y=y') by exact (renaming_equivalent_lookup_determinacy M b c n b' c' n' k d y y' Heq Hy Hy').
  subst x' y'. exact (renaming_atom_functional M equality x y t k v w Hout Hout').
Qed.

Lemma renaming_functional_binary M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  renaming_functional_at M a -> renaming_functional_at M d -> renaming_functional_at M f.
Proof.
  intros Hh Hf IHa IHd b c n b' c' n' k t v w Heq Hv Hw.
  destruct (renaming_computation_binary_inv M h a d f b c n k t v Hh Hf Hv)
    as [x [y [Hx [Hy Hout]]]].
  destruct (renaming_computation_binary_inv M h a d f b' c' n' k t w Hh Hf Hw)
    as [x' [y' [Hx' [Hy' Hout']]]].
  assert (Ex : x=x') by exact (IHa b c n b' c' n' k t x x' Heq Hx Hx').
  assert (Ey : y=y') by exact (IHd b c n b' c' n' k t y y' Heq Hy Hy').
  subst x' y'. exact (renaming_binary_functional M h x y v w Hout Hout').
Qed.

Lemma renaming_functional_unary M universal a f :
  sf_relation M (renaming_source_quantifier universal) a (zeroM M) f ->
  renaming_functional_at M a -> renaming_functional_at M f.
Proof.
  intros Hf IH b c n b' c' n' k t v w Heq Hv Hw.
  destruct (renaming_computation_unary_inv M universal a f b c n k t v Hf Hv)
    as [d [e [m [x [Hcons [Hx Hout]]]]]].
  destruct (renaming_computation_unary_inv M universal a f b' c' n' k t w Hf Hw)
    as [d' [e' [m' [y [Hcons' [Hy Hout']]]]]].
  assert (Hchild : renaming_equivalent M d e m d' e' m' k).
  { exact (renaming_lift_extensional M b c n b' c' n' k d e m d' e' m' Heq Hcons Hcons'). }
  assert (Ex : x=y) by exact (IH d e m d' e' m' k t x y Hchild Hx Hy).
  subst y. exact (renaming_quantifier_functional M universal k t x v w Hout Hout').
Qed.

Theorem renaming_computation_functional_equivalent M f : renaming_functional_at M f.
Proof.
  revert f. apply (sf_code_induction M (renaming_functional_at M)).
  - apply renaming_functional_at_definable.
  - intros b c n d e m k t v w Heq Hv Hw.
    rewrite (renaming_computation_invalid M (zeroM M) b c n k t v (or_introl eq_refl) Hv),
      (renaming_computation_invalid M (zeroM M) d e m k t w (or_introl eq_refl) Hw). reflexivity.
  - intros f Hbad b c n d e m k t v w Heq Hv Hw.
    rewrite (renaming_computation_invalid M f b c n k t v (or_intror Hbad) Hv),
      (renaming_computation_invalid M f d e m k t w (or_intror Hbad) Hw). reflexivity.
  - intros a d f Hf. exact (renaming_functional_atom M false a d f Hf).
  - intros a d f Hf. exact (renaming_functional_atom M true a d f Hf).
  - exact (renaming_functional_binary M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (renaming_functional_unary M true a f Hf IH).
    + exact (renaming_functional_unary M false a f Hf IH).
Qed.

Corollary renaming_computation_functional M f b c n k t v w :
  renaming_computation M f b c n k t v -> renaming_computation M f b c n k t w -> v=w.
Proof.
  apply (renaming_computation_functional_equivalent M f b c n b c n k t v w).
  apply renaming_equivalent_refl.
Qed.

Corollary renaming_computation_environment_extensional M f b c n d e m k t v :
  renaming_equivalent M b c n d e m k ->
  (renaming_computation M f b c n k t v <-> renaming_computation M f d e m k t v).
Proof.
  intro Heq. split; intro Hv.
  - destruct (renaming_computation_total M f d e m k t) as [w Hw].
    assert (E : v=w) by exact (renaming_computation_functional_equivalent M f b c n d e m k t v w Heq Hv Hw).
    now subst w.
  - destruct (renaming_computation_total M f b c n k t) as [w Hw].
    assert (E : w=v) by exact (renaming_computation_functional_equivalent M f b c n d e m k t w v Heq Hw Hv).
    now subst w.
Qed.
