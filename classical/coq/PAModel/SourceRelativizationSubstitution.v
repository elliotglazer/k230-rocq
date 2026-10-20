(** Relativization commutes with the actual internally coded de Bruijn
    substitution.  The domain has at most its distinguished free index zero. *)
From PAModel Require Import Model CodeExpressions NumericalProofs SetFormulaCodes
  SetCodeDescent SourceBounded NumericalSubstitutionMaps NumericalSubstitution
  SourceSubstitutionIdentity SourceRelativizationRules SourceRelativization
  SourceRelativizationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma sr_quantifier_substitution M universal domain w r b c n base d e m w' s :
  source_bounded M domain (code_numeral M 1) ->
  substitution_lift M b c n base d e m ->
  sr_quantifier M universal domain w r ->
  numerical_substitution M w d e m (succM M base) w' ->
  sr_quantifier M universal domain w' s ->
  numerical_substitution M r b c n base s.
Proof.
  intros HD HL [u [HU HR]] HW [v [HV HS]].
  pose proof (numerical_substitution_lift_fixes_domain M domain b c n base d e m HD HL) as HId.
  destruct universal.
  - apply (proj2 (numerical_substitution_quantifier M true u r b c n base s HR)).
    exists d,e,m,v. split;[exact HL|]. split;[|exact HS].
    apply (proj2 (numerical_substitution_binary M SFImpl domain w u d e m (succM M base) v
      (or_intror (or_intror eq_refl)) HU)).
    exists domain,w'. auto.
  - apply (proj2 (numerical_substitution_quantifier M false u r b c n base s HR)).
    exists d,e,m,v. split;[exact HL|]. split;[|exact HS].
    apply (proj2 (numerical_substitution_binary M SFAnd domain w u d e m (succM M base) v
      (or_introl eq_refl) HU)).
    exists domain,w'. auto.
Qed.

Definition sr_substitution_property M f := forall domain b c n base g r,
  source_bounded M domain (code_numeral M 1) ->
  numerical_substitution M f b c n base g -> source_relativization M domain f r ->
  exists s, source_relativization M domain g s /\ numerical_substitution M r b c n base s.

Definition sr_substitution_formula : form :=
  ∀∀∀∀∀∀∀ (source_bounded_accept_formula $6 (num 1) →
    numerical_substitution_formula $7 $5 $4 $3 $2 $1 →
    source_relativization_formula $6 $7 $0 →
    ∃ (source_relativization_formula $7 $2 $0 ∧
       numerical_substitution_formula $1 $6 $5 $4 $3 $0)).

Local Opaque holds source_bounded_accept_formula numerical_substitution_formula
  source_relativization_formula.
Lemma sr_substitution_property_definable M : Definable1 M (sr_substitution_property M).
Proof.
  exists sr_substitution_formula,(fun _=>zeroM M). intro f.
  unfold sr_substitution_formula,sr_substitution_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite source_relativization_formula_correct. reflexivity.
Qed.

Lemma sr_substitution_invalid M f domain b c n base g r :
  (f=zeroM M \/ sf_invalid M f) ->
  numerical_substitution M f b c n base g -> source_relativization M domain f r ->
  exists s,source_relativization M domain g s /\ numerical_substitution M r b c n base s.
Proof.
  intros HBad HG HR.
  pose proof (proj1 (numerical_substitution_invalid M f b c n base g HBad) HG) as EG.
  pose proof (source_relativization_invalid_inv M domain f r HBad HR) as ER.
  subst g r. exists (zeroM M). split;[apply source_relativization_falsity|].
  apply (proj2 (numerical_substitution_invalid M (zeroM M) b c n base
    (zeroM M) (or_introl eq_refl))). reflexivity.
Qed.

Lemma sr_substitution_atom M equality a z f domain b c n base g r :
  sf_relation M (sr_source_atom equality) a z f ->
  numerical_substitution M f b c n base g -> source_relativization M domain f r ->
  exists s,source_relativization M domain g s /\ numerical_substitution M r b c n base s.
Proof.
  intros HF HG HR.
  pose proof (source_relativization_atom_inv M domain equality a z f r HF HR) as ER.
  subst r. exists g. split;[|exact HG].
  destruct (proj1 (numerical_substitution_atom M equality a z f b c n base g HF) HG)
    as [x [y [_ [_ HShape]]]].
  apply (source_relativization_atom M domain (sr_source_atom equality) x y g).
  - destruct equality;[right|left];reflexivity.
  - exact HShape.
Qed.

Theorem source_relativization_substitution_exists M f : sr_substitution_property M f.
Proof.
  revert f. apply (sf_code_induction M (sr_substitution_property M)).
  - apply sr_substitution_property_definable.
  - intros domain b c n base g r _ HG HR.
    exact (sr_substitution_invalid M (zeroM M) domain b c n base g r (or_introl eq_refl) HG HR).
  - intros f HBad domain b c n base g r _ HG HR.
    exact (sr_substitution_invalid M f domain b c n base g r (or_intror HBad) HG HR).
  - intros a z f HF domain b c n base g r _ HG HR.
    exact (sr_substitution_atom M false a z f domain b c n base g r HF HG HR).
  - intros a z f HF domain b c n base g r _ HG HR.
    exact (sr_substitution_atom M true a z f domain b c n base g r HF HG HR).
  - intros h a z f Hh HF IHa IHz domain b c n base g r HD HG HR.
    destruct (proj1 (numerical_substitution_binary M h a z f b c n base g Hh HF) HG)
      as [a' [z' [HA [HZ HShapeG]]]].
    destruct (source_relativization_binary_inv M domain h a z f r Hh HF HR)
      as [ar [zr [HAR [HZR HShapeR]]]].
    destruct (IHa domain b c n base a' ar HD HA HAR) as [as' [HAS RAS]].
    destruct (IHz domain b c n base z' zr HD HZ HZR) as [zs' [HZS RZS]].
    destruct (sf_relation_total M h as' zs') as [s HShapeS]. exists s. split.
    + exact (source_relativization_binary M domain h a' z' g as' zs' s
        Hh HShapeG HAS HZS HShapeS).
    + apply (proj2 (numerical_substitution_binary M h ar zr r b c n base s Hh HShapeR)).
      exists as',zs'. auto.
  - intros h a f Hh HF IH domain b c n base g r HD HG HR.
    assert (Hex:exists universal,h=sr_source_quantifier universal).
    { destruct Hh as [E|E];subst h;[exists true|exists false];reflexivity. }
    destruct Hex as [universal E]. subst h.
    destruct (proj1 (numerical_substitution_quantifier M universal a f b c n base g HF) HG)
      as [d [e [m [a' [HL [HA HShapeG]]]]]].
    destruct (source_relativization_quantifier_inv M domain universal a f r HF HR)
      as [ar [HAR HShapeR]].
    destruct (IH domain d e m (succM M base) a' ar HD HA HAR) as [as' [HAS RAS]].
    destruct (sr_quantifier_total M universal domain as') as [s HShapeS]. exists s. split.
    + exact (source_relativization_quantifier M domain universal a' g as' s HShapeG HAS HShapeS).
    + exact (sr_quantifier_substitution M universal domain ar r b c n base d e m as' s
        HD HL HShapeR RAS HShapeS).
Qed.

Theorem source_relativization_substitution M domain f r b c n base g s :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f r -> numerical_substitution M f b c n base g ->
  numerical_substitution M r b c n base s -> source_relativization M domain g s.
Proof.
  intros HD HR HG HS.
  destruct (source_relativization_substitution_exists M f domain b c n base g r HD HG HR)
    as [s' [HR' HS']].
  rewrite (numerical_substitution_functional M r b c n base s s' HS HS'). exact HR'.
Qed.

Print Assumptions source_relativization_substitution_exists.
Print Assumptions source_relativization_substitution.
