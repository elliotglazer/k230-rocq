(** Bound preservation for internally certified de Bruijn renaming.
    Source codes, bounds, and prefix-map lengths are arbitrary model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula NumericalProofs NumericalEnvironments SetFormulaCodes
  SetCodeDescent SourceBounded NumericalRenamingMaps RenamingPayloads NumericalRenaming.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition renaming_maps_bound M b c n delta k l :=
  forall i j, coding_lt M i k -> renaming_lookup M b c n delta i j -> coding_lt M j l.

Definition renaming_maps_bound_formula (b c n delta k l : term) : form :=
  ∀∀ (Peano.sless $1 (environment_lift2 k) →
    renaming_lookup_formula (environment_lift2 b) (environment_lift2 c)
      (environment_lift2 n) (environment_lift2 delta) $1 $0 →
    Peano.sless $0 (environment_lift2 l)).

Local Opaque holds renaming_lookup_formula.
Lemma renaming_maps_bound_formula_correct M rho b c n delta k l :
  holds M rho (renaming_maps_bound_formula b c n delta k l) <->
  renaming_maps_bound M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho delta) (evalM M rho k) (evalM M rho l).
Proof.
  unfold renaming_maps_bound_formula,renaming_maps_bound.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite renaming_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.

Theorem renaming_lift_maps_bound M b c n delta d e m k l :
  renaming_lift M b c n delta d e m ->
  renaming_maps_bound M b c n delta k l ->
  renaming_maps_bound M d e m delta (succM M k) (succM M l).
Proof.
  intros Hlift Hbound i j Hi Hj.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[i' E]]; subst i.
  - apply (proj1 (renaming_lift_head M b c n delta d e m j Hlift)) in Hj.
    subst j. apply coding_zero_lt_succ.
  - destruct (renaming_lift_tail_inv M b c n delta d e m i' j Hlift Hj)
      as [j' [Hj' E]]. subst j.
    apply coding_lt_succ_cancel. apply (Hbound i' j').
    + exact (proj1 (coding_lt_succ_cancel M i' k) Hi).
    + exact Hj'.
Qed.

Definition source_renaming_bound_property M f := forall b c n delta g k l,
  source_bounded M f k -> numerical_renaming M f b c n delta g ->
  renaming_maps_bound M b c n delta k l -> source_bounded M g l.

Definition source_renaming_bound_property_formula : form :=
  ∀∀∀∀∀∀∀ (source_bounded_accept_formula $7 $1 →
    numerical_renaming_formula $7 $6 $5 $4 $3 $2 →
    renaming_maps_bound_formula $6 $5 $4 $3 $1 $0 →
    source_bounded_accept_formula $2 $0).

Local Opaque source_bounded_accept_formula numerical_renaming_formula renaming_maps_bound_formula.
Lemma source_renaming_bound_property_definable M :
  Definable1 M (source_renaming_bound_property M).
Proof.
  exists source_renaming_bound_property_formula,(fun _ => zeroM M). intro f.
  unfold source_renaming_bound_property_formula,source_renaming_bound_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite renaming_maps_bound_formula_correct. reflexivity.
Qed.

Theorem numerical_renaming_preserves_bound M root : source_renaming_bound_property M root.
Proof.
  apply (sf_code_induction M (source_renaming_bound_property M)).
  - apply source_renaming_bound_property_definable.
  - intros b c n delta g k l _ Hr _.
    apply (proj1 (numerical_renaming_invalid M (zeroM M) b c n delta g (or_introl eq_refl))) in Hr.
    subst g. apply source_bounded_accept_falsity.
  - intros f Hbad b c n delta g k l Hf _ _.
    exfalso. exact (source_bounded_reject_invalid M f k Hbad Hf).
  - intros a d f Hf b c n delta g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_atom M SFMember a d f k (or_introl eq_refl) Hf)) in Hb.
    apply (proj1 (numerical_renaming_member M a d f b c n delta g Hf)) in Hr.
    destruct Hb as [Ha Hd], Hr as [x [y [Hx [Hy Hg]]]].
    apply (proj2 (source_bounded_accept_atom M SFMember x y g l (or_introl eq_refl) Hg)).
    split; [exact (Hmap a x Ha Hx)|exact (Hmap d y Hd Hy)].
  - intros a d f Hf b c n delta g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_atom M SFEqual a d f k (or_intror eq_refl) Hf)) in Hb.
    apply (proj1 (numerical_renaming_equal M a d f b c n delta g Hf)) in Hr.
    destruct Hb as [Ha Hd], Hr as [x [y [Hx [Hy Hg]]]].
    apply (proj2 (source_bounded_accept_atom M SFEqual x y g l (or_intror eq_refl) Hg)).
    split; [exact (Hmap a x Ha Hx)|exact (Hmap d y Hd Hy)].
  - intros h a d f Hh Hf IHa IHd b c n delta g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_binary M h a d f k Hh Hf)) in Hb.
    apply (proj1 (numerical_renaming_binary M h a d f b c n delta g Hh Hf)) in Hr.
    destruct Hb as [Ha Hd], Hr as [x [y [Hx [Hy Hg]]]].
    apply (proj2 (source_bounded_accept_binary M h x y g l Hh Hg)).
    split; [exact (IHa b c n delta x k l Ha Hx Hmap)|exact (IHd b c n delta y k l Hd Hy Hmap)].
  - intros h a f Hh Hf IH b c n delta g k l Hb Hr Hmap.
    apply (proj1 (source_bounded_accept_unary M h a f k Hh Hf)) in Hb.
    assert (Hex : exists universal, h=renaming_source_quantifier universal).
    { destruct Hh as [He|He]; subst h; [exists true|exists false]; reflexivity. }
    destruct Hex as [universal ->].
    apply (proj1 (numerical_renaming_quantifier M universal a f b c n delta g Hf)) in Hr.
    destruct Hr as [d [e [m [w [Hlift [Hw Hg]]]]]].
    apply (proj2 (source_bounded_accept_unary M (renaming_source_quantifier universal) w g l Hh Hg)).
    apply (IH d e m delta w (succM M k) (succM M l) Hb Hw).
    exact (renaming_lift_maps_bound M b c n delta d e m k l Hlift Hmap).
Qed.

Corollary numerical_renaming_closed M f b c n delta g :
  source_bounded M f (zeroM M) -> numerical_renaming M f b c n delta g ->
  source_bounded M g (zeroM M).
Proof.
  intros Hb Hr. apply (numerical_renaming_preserves_bound M f b c n delta g
    (zeroM M) (zeroM M) Hb Hr). intros i j Hi _.
  exfalso. exact (coding_not_lt_zero M i Hi).
Qed.




