(** Relativization commutes with the actual internally coded de Bruijn
    renaming.  The domain has at most its distinguished free index zero. *)
From PAModel Require Import Model CodeExpressions NumericalProofs SetFormulaCodes
  SetCodeDescent SourceBounded NumericalRenamingMaps NumericalRenaming
  SourceRenamingIdentity SourceRelativizationRules SourceRelativization
  SourceRelativizationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma sr_quantifier_renaming M universal domain w r b c n delta d e m w' s :
  source_bounded M domain (code_numeral M 1) ->
  renaming_lift M b c n delta d e m ->
  sr_quantifier M universal domain w r ->
  numerical_renaming M w d e m delta w' ->
  sr_quantifier M universal domain w' s ->
  numerical_renaming M r b c n delta s.
Proof.
  intros HD HL [u [HU HR]] HW [v [HV HS]].
  pose proof (numerical_renaming_lift_fixes_domain M domain b c n delta d e m HD HL) as HId.
  destruct universal.
  - apply (proj2 (numerical_renaming_quantifier M true u r b c n delta s HR)).
    exists d,e,m,v. split;[exact HL|]. split;[|exact HS].
    apply (proj2 (numerical_renaming_binary M SFImpl domain w u d e m delta v
      (or_intror (or_intror eq_refl)) HU)).
    exists domain,w'. auto.
  - apply (proj2 (numerical_renaming_quantifier M false u r b c n delta s HR)).
    exists d,e,m,v. split;[exact HL|]. split;[|exact HS].
    apply (proj2 (numerical_renaming_binary M SFAnd domain w u d e m delta v
      (or_introl eq_refl) HU)).
    exists domain,w'. auto.
Qed.

Definition sr_renaming_property M f := forall domain b c n delta g r,
  source_bounded M domain (code_numeral M 1) ->
  numerical_renaming M f b c n delta g -> source_relativization M domain f r ->
  exists s, source_relativization M domain g s /\ numerical_renaming M r b c n delta s.

Definition sr_renaming_formula : form :=
  ∀∀∀∀∀∀∀ (source_bounded_accept_formula $6 (num 1) →
    numerical_renaming_formula $7 $5 $4 $3 $2 $1 →
    source_relativization_formula $6 $7 $0 →
    ∃ (source_relativization_formula $7 $2 $0 ∧
       numerical_renaming_formula $1 $6 $5 $4 $3 $0)).

Local Opaque holds source_bounded_accept_formula numerical_renaming_formula
  source_relativization_formula.
Lemma sr_renaming_property_definable M : Definable1 M (sr_renaming_property M).
Proof.
  exists sr_renaming_formula,(fun _=>zeroM M). intro f.
  unfold sr_renaming_formula,sr_renaming_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_relativization_formula_correct. reflexivity.
Qed.

Lemma sr_renaming_invalid M f domain b c n delta g r :
  (f=zeroM M \/ sf_invalid M f) ->
  numerical_renaming M f b c n delta g -> source_relativization M domain f r ->
  exists s,source_relativization M domain g s /\ numerical_renaming M r b c n delta s.
Proof.
  intros HBad HG HR.
  pose proof (proj1 (numerical_renaming_invalid M f b c n delta g HBad) HG) as EG.
  pose proof (source_relativization_invalid_inv M domain f r HBad HR) as ER.
  subst g r. exists (zeroM M). split;[apply source_relativization_falsity|].
  apply (proj2 (numerical_renaming_invalid M (zeroM M) b c n delta
    (zeroM M) (or_introl eq_refl))). reflexivity.
Qed.

Lemma sr_renaming_atom M equality a z f domain b c n delta g r :
  sf_relation M (sr_source_atom equality) a z f ->
  numerical_renaming M f b c n delta g -> source_relativization M domain f r ->
  exists s,source_relativization M domain g s /\ numerical_renaming M r b c n delta s.
Proof.
  intros HF HG HR.
  pose proof (source_relativization_atom_inv M domain equality a z f r HF HR) as ER.
  subst r. exists g. split;[|exact HG].
  destruct (proj1 (numerical_renaming_atom M equality a z f b c n delta g HF) HG)
    as [x [y [_ [_ HShape]]]].
  apply (source_relativization_atom M domain (sr_source_atom equality) x y g).
  - destruct equality;[right|left];reflexivity.
  - exact HShape.
Qed.

Theorem source_relativization_renaming_exists M f : sr_renaming_property M f.
Proof.
  revert f. apply (sf_code_induction M (sr_renaming_property M)).
  - apply sr_renaming_property_definable.
  - intros domain b c n delta g r _ HG HR.
    exact (sr_renaming_invalid M (zeroM M) domain b c n delta g r (or_introl eq_refl) HG HR).
  - intros f HBad domain b c n delta g r _ HG HR.
    exact (sr_renaming_invalid M f domain b c n delta g r (or_intror HBad) HG HR).
  - intros a z f HF domain b c n delta g r _ HG HR.
    exact (sr_renaming_atom M false a z f domain b c n delta g r HF HG HR).
  - intros a z f HF domain b c n delta g r _ HG HR.
    exact (sr_renaming_atom M true a z f domain b c n delta g r HF HG HR).
  - intros h a z f Hh HF IHa IHz domain b c n delta g r HD HG HR.
    destruct (proj1 (numerical_renaming_binary M h a z f b c n delta g Hh HF) HG)
      as [a' [z' [HA [HZ HShapeG]]]].
    destruct (source_relativization_binary_inv M domain h a z f r Hh HF HR)
      as [ar [zr [HAR [HZR HShapeR]]]].
    destruct (IHa domain b c n delta a' ar HD HA HAR) as [as' [HAS RAS]].
    destruct (IHz domain b c n delta z' zr HD HZ HZR) as [zs' [HZS RZS]].
    destruct (sf_relation_total M h as' zs') as [s HShapeS]. exists s. split.
    + exact (source_relativization_binary M domain h a' z' g as' zs' s
        Hh HShapeG HAS HZS HShapeS).
    + apply (proj2 (numerical_renaming_binary M h ar zr r b c n delta s Hh HShapeR)).
      exists as',zs'. auto.
  - intros h a f Hh HF IH domain b c n delta g r HD HG HR.
    assert (Hex:exists universal,h=sr_source_quantifier universal).
    { destruct Hh as [E|E];subst h;[exists true|exists false];reflexivity. }
    destruct Hex as [universal E]. subst h.
    destruct (proj1 (numerical_renaming_quantifier M universal a f b c n delta g HF) HG)
      as [d [e [m [a' [HL [HA HShapeG]]]]]].
    destruct (source_relativization_quantifier_inv M domain universal a f r HF HR)
      as [ar [HAR HShapeR]].
    destruct (IH domain d e m delta a' ar HD HA HAR) as [as' [HAS RAS]].
    destruct (sr_quantifier_total M universal domain as') as [s HShapeS]. exists s. split.
    + exact (source_relativization_quantifier M domain universal a' g as' s HShapeG HAS HShapeS).
    + exact (sr_quantifier_renaming M universal domain ar r b c n delta d e m as' s
        HD HL HShapeR RAS HShapeS).
Qed.

Theorem source_relativization_renaming M domain f r b c n delta g s :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f r -> numerical_renaming M f b c n delta g ->
  numerical_renaming M r b c n delta s -> source_relativization M domain g s.
Proof.
  intros HD HR HG HS.
  destruct (source_relativization_renaming_exists M f domain b c n delta g r HD HG HR)
    as [s' [HR' HS']].
  rewrite (numerical_renaming_functional M r b c n delta s s' HS HS'). exact HR'.
Qed.

Print Assumptions source_relativization_renaming_exists.
Print Assumptions source_relativization_renaming.
