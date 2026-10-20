(** Bound preservation for internally certified de Bruijn substitution.
    Source codes, bounds, and prefix-map lengths are arbitrary model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula NumericalProofs NumericalEnvironments SetFormulaCodes
  SetCodeDescent SourceBounded NumericalSubstitutionMaps SubstitutionPayloads
  SubstitutionRules NumericalSubstitution SubstitutionSource.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_maps_bound M b c n base k l :=
  forall i j, coding_lt M i k -> substitution_lookup M b c n base i j -> coding_lt M j l.

Definition substitution_maps_bound_formula (b c n base k l : term) : form :=
  ∀∀ (Peano.sless $1 (environment_lift2 k) →
    substitution_lookup_formula (environment_lift2 b) (environment_lift2 c)
      (environment_lift2 n) (environment_lift2 base) $1 $0 →
    Peano.sless $0 (environment_lift2 l)).

Local Opaque holds substitution_lookup_formula.
Lemma substitution_maps_bound_formula_correct M rho b c n base k l :
  holds M rho (substitution_maps_bound_formula b c n base k l) <->
  substitution_maps_bound M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho base) (evalM M rho k) (evalM M rho l).
Proof.
  unfold substitution_maps_bound_formula,substitution_maps_bound.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.

Theorem substitution_lift_maps_bound M b c n base d e m k l :
  substitution_lift M b c n base d e m ->
  substitution_maps_bound M b c n base k l ->
  substitution_maps_bound M d e m (succM M base) (succM M k) (succM M l).
Proof.
  intros Hlift Hbound i j Hi Hj.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[i' E]]; subst i.
  - apply (proj1 (substitution_lift_head M b c n base d e m j Hlift)) in Hj.
    subst j. apply coding_zero_lt_succ.
  - destruct (substitution_lift_tail_inv M b c n base d e m i' j Hlift Hj)
      as [j' [Hj' E]]. subst j.
    apply coding_lt_succ_cancel. apply (Hbound i' j').
    + exact (proj1 (coding_lt_succ_cancel M i' k) Hi).
    + exact Hj'.
Qed.

Definition source_substitution_bound_property M f := forall b c n base g k l,
  source_bounded M f k -> numerical_substitution M f b c n base g ->
  substitution_maps_bound M b c n base k l -> source_bounded M g l.

Definition source_substitution_bound_property_formula : form :=
  ∀∀∀∀∀∀∀ (source_bounded_accept_formula $7 $1 →
    numerical_substitution_formula $7 $6 $5 $4 $3 $2 →
    substitution_maps_bound_formula $6 $5 $4 $3 $1 $0 →
    source_bounded_accept_formula $2 $0).

Local Opaque source_bounded_accept_formula numerical_substitution_formula substitution_maps_bound_formula.
Lemma source_substitution_bound_property_definable M :
  Definable1 M (source_substitution_bound_property M).
Proof.
  exists source_substitution_bound_property_formula,(fun _ => zeroM M). intro f.
  unfold source_substitution_bound_property_formula,source_substitution_bound_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite substitution_maps_bound_formula_correct. reflexivity.
Qed.

Theorem numerical_substitution_preserves_bound M root : source_substitution_bound_property M root.
Proof.
  apply (sf_code_induction M (source_substitution_bound_property M)).
  - apply source_substitution_bound_property_definable.
  - intros b c n base g k l _ Hr _.
    apply (proj1 (numerical_substitution_invalid M (zeroM M) b c n base g (or_introl eq_refl))) in Hr.
    subst g. apply source_bounded_accept_falsity.
  - intros f Hbad b c n base g k l Hf _ _.
    exfalso. exact (source_bounded_reject_invalid M f k Hbad Hf).
  - intros a d f Hf b c n base g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_atom M SFMember a d f k (or_introl eq_refl) Hf)) in Hb.
    apply (proj1 (numerical_substitution_member M a d f b c n base g Hf)) in Hr.
    destruct Hb as [Ha Hd], Hr as [x [y [Hx [Hy Hg]]]].
    apply (proj2 (source_bounded_accept_atom M SFMember x y g l (or_introl eq_refl) Hg)).
    split; [exact (Hmap a x Ha Hx)|exact (Hmap d y Hd Hy)].
  - intros a d f Hf b c n base g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_atom M SFEqual a d f k (or_intror eq_refl) Hf)) in Hb.
    apply (proj1 (numerical_substitution_equal M a d f b c n base g Hf)) in Hr.
    destruct Hb as [Ha Hd], Hr as [x [y [Hx [Hy Hg]]]].
    apply (proj2 (source_bounded_accept_atom M SFEqual x y g l (or_intror eq_refl) Hg)).
    split; [exact (Hmap a x Ha Hx)|exact (Hmap d y Hd Hy)].
  - intros h a d f Hh Hf IHa IHd b c n base g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_binary M h a d f k Hh Hf)) in Hb.
    apply (proj1 (numerical_substitution_binary M h a d f b c n base g Hh Hf)) in Hr.
    destruct Hb as [Ha Hd], Hr as [x [y [Hx [Hy Hg]]]].
    apply (proj2 (source_bounded_accept_binary M h x y g l Hh Hg)).
    split; [exact (IHa b c n base x k l Ha Hx Hmap)|exact (IHd b c n base y k l Hd Hy Hmap)].
  - intros h a f Hh Hf IH b c n base g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_unary M h a f k Hh Hf)) in Hb.
    assert (Hex : exists universal, h=substitution_source_quantifier universal).
    { destruct Hh as [He|He]; subst h; [exists true|exists false]; reflexivity. }
    destruct Hex as [universal ->].
    apply (proj1 (numerical_substitution_quantifier M universal a f b c n base g Hf)) in Hr.
    destruct Hr as [d [e [m [w [Hlift [Hw Hg]]]]]].
    apply (proj2 (source_bounded_accept_unary M (substitution_source_quantifier universal) w g l Hh Hg)).
    apply (IH d e m (succM M base) w (succM M k) (succM M l) Hb Hw).
    exact (substitution_lift_maps_bound M b c n base d e m k l Hlift Hmap).
Qed.

Corollary numerical_substitution_closed M f b c n base g :
  source_bounded M f (zeroM M) -> numerical_substitution M f b c n base g ->
  source_bounded M g (zeroM M).
Proof.
  intros Hb Hr. apply (numerical_substitution_preserves_bound M f b c n base g
    (zeroM M) (zeroM M) Hb Hr). intros i j Hi _.
  exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Theorem substitution_singleton_maps_bound M b c t k :
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
  coding_lt M t k ->
  substitution_maps_bound M b c (succM M (zeroM M)) (zeroM M) (succM M k) k.
Proof.
  intros Hhead Ht i j Hi Hj.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [Ei|[i' Ei]]; subst i.
  - assert (E : j=t) by (eapply substitution_lookup_functional; eassumption).
    now subst j.
  - assert (E : j=i').
    { eapply substitution_lookup_functional; [exact Hj|apply substitution_singleton_tail]. }
    subst j. exact (proj1 (coding_lt_succ_cancel M i' k) Hi).
Qed.

Theorem numerical_substitution_singleton_bound M f b c t k g :
  source_bounded M f (succM M k) -> coding_lt M t k ->
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
  numerical_substitution M f b c (succM M (zeroM M)) (zeroM M) g ->
  source_bounded M g k.
Proof.
  intros Hf Ht Hhead Hg.
  apply (numerical_substitution_preserves_bound M f b c (succM M (zeroM M))
    (zeroM M) g (succM M k) k Hf Hg).
  exact (substitution_singleton_maps_bound M b c t k Hhead Ht).
Qed.

Print Assumptions substitution_maps_bound_formula_correct.
Print Assumptions numerical_substitution_preserves_bound.
Print Assumptions numerical_substitution_singleton_bound.






