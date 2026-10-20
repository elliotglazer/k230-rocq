(** Moving-carrier set relativization commutes with actual internal
    renaming, including the carrier lookup and its lifted quantified child. *)
From PAModel Require Import Model CodeExpressions NumericalProofs SetFormulaCodes
  SetCodeDescent SourceBounded NumericalRenamingMaps NumericalRenaming
  SourceRenamingIdentity SourceRelativizationRules SourceRelativization
  SourceRelativizationFunctionality SourceSetRelativization SourceSetRelativizationRules
  SourceSetRelativizationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma ssr_quantifier_renaming M universal carrier carrier' w r b c n delta d e m w' s :
  renaming_lookup M b c n delta carrier carrier' ->
  renaming_lift M b c n delta d e m ->
  ssr_quantifier M universal carrier w r ->
  numerical_renaming M w d e m delta w' ->
  ssr_quantifier M universal carrier' w' s ->
  numerical_renaming M r b c n delta s.
Proof.
  intros HCarrier HL (guard&mid&HG&HM&HR) HW (guard'&mid'&HG'&HM'&HS).
  assert (HGuard:numerical_renaming M guard d e m delta guard').
  { apply (proj2(numerical_renaming_atom M false (zeroM M)(succM M carrier)guard d e m delta guard' HG)).
    exists(zeroM M),(succM M carrier'). split;[exact(proj1(proj2 HL))|]. split;[|exact HG'].
    exact(proj2(proj2 HL) carrier carrier' HCarrier). }
  destruct universal.
  - apply(proj2(numerical_renaming_quantifier M true mid r b c n delta s HR)).
    exists d,e,m,mid'. split;[exact HL|]. split;[|exact HS].
    apply(proj2(numerical_renaming_binary M SFImpl guard w mid d e m delta mid'
      (or_intror(or_intror eq_refl)) HM)). exists guard',w'. auto.
  - apply(proj2(numerical_renaming_quantifier M false mid r b c n delta s HR)).
    exists d,e,m,mid'. split;[exact HL|]. split;[|exact HS].
    apply(proj2(numerical_renaming_binary M SFAnd guard w mid d e m delta mid'
      (or_introl eq_refl) HM)). exists guard',w'. auto.
Qed.

Definition ssr_renaming_property M f := forall carrier carrier' b c n delta g r,
  renaming_lookup M b c n delta carrier carrier' ->
  numerical_renaming M f b c n delta g -> source_set_relativization M carrier f r ->
  exists s, source_set_relativization M carrier' g s /\ numerical_renaming M r b c n delta s.

Definition ssr_renaming_formula : form :=
  ∀∀∀∀∀∀∀∀ (renaming_lookup_formula $5 $4 $3 $2 $7 $6 →
    numerical_renaming_formula $8 $5 $4 $3 $2 $1 →
    source_set_relativization_formula $7 $8 $0 →
    ∃ (source_set_relativization_formula $7 $2 $0 ∧
       numerical_renaming_formula $1 $6 $5 $4 $3 $0)).

Local Opaque holds renaming_lookup_formula numerical_renaming_formula
  source_set_relativization_formula.
Lemma ssr_renaming_property_definable M : Definable1 M (ssr_renaming_property M).
Proof.
  exists ssr_renaming_formula,(fun _=>zeroM M). intro f.
  unfold ssr_renaming_formula,ssr_renaming_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite renaming_lookup_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_set_relativization_formula_correct. reflexivity.
Qed.

Lemma ssr_renaming_invalid M f carrier carrier' b c n delta g r :
  (f=zeroM M \/ sf_invalid M f) ->
  numerical_renaming M f b c n delta g -> source_set_relativization M carrier f r ->
  exists s,source_set_relativization M carrier' g s /\ numerical_renaming M r b c n delta s.
Proof.
  intros HBad HG HR.
  pose proof (proj1 (numerical_renaming_invalid M f b c n delta g HBad) HG) as EG.
  pose proof (source_set_relativization_invalid_inv M carrier f r HBad HR) as ER.
  subst g r. exists (zeroM M). split;[apply source_set_relativization_falsity|].
  apply (proj2 (numerical_renaming_invalid M (zeroM M) b c n delta
    (zeroM M) (or_introl eq_refl))). reflexivity.
Qed.

Lemma ssr_renaming_atom M equality a z f carrier carrier' b c n delta g r :
  sf_relation M (sr_source_atom equality) a z f ->
  numerical_renaming M f b c n delta g -> source_set_relativization M carrier f r ->
  exists s,source_set_relativization M carrier' g s /\ numerical_renaming M r b c n delta s.
Proof.
  intros HF HG HR.
  pose proof (source_set_relativization_atom_inv M carrier equality a z f r HF HR) as ER.
  subst r. exists g. split;[|exact HG].
  destruct (proj1 (numerical_renaming_atom M equality a z f b c n delta g HF) HG)
    as [x [y [_ [_ HShape]]]].
  apply (source_set_relativization_atom M carrier' (sr_source_atom equality) x y g).
  - destruct equality;[right|left];reflexivity.
  - exact HShape.
Qed.

Theorem source_set_relativization_renaming_exists M f : ssr_renaming_property M f.
Proof.
  revert f. apply (sf_code_induction M (ssr_renaming_property M)).
  - apply ssr_renaming_property_definable.
  - intros carrier carrier' b c n delta g r HD HG HR.
    exact (ssr_renaming_invalid M (zeroM M) carrier carrier' b c n delta g r (or_introl eq_refl) HG HR).
  - intros f HBad carrier carrier' b c n delta g r _ HG HR.
    exact (ssr_renaming_invalid M f carrier carrier' b c n delta g r (or_intror HBad) HG HR).
  - intros a z f HF carrier carrier' b c n delta g r _ HG HR.
    exact (ssr_renaming_atom M false a z f carrier carrier' b c n delta g r HF HG HR).
  - intros a z f HF carrier carrier' b c n delta g r _ HG HR.
    exact (ssr_renaming_atom M true a z f carrier carrier' b c n delta g r HF HG HR).
  - intros h a z f Hh HF IHa IHz carrier carrier' b c n delta g r HD HG HR.
    destruct (proj1 (numerical_renaming_binary M h a z f b c n delta g Hh HF) HG)
      as [a' [z' [HA [HZ HShapeG]]]].
    destruct (source_set_relativization_binary_inv M carrier h a z f r Hh HF HR)
      as [ar [zr [HAR [HZR HShapeR]]]].
    destruct (IHa carrier carrier' b c n delta a' ar HD HA HAR) as [as' [HAS RAS]].
    destruct (IHz carrier carrier' b c n delta z' zr HD HZ HZR) as [zs' [HZS RZS]].
    destruct (sf_relation_total M h as' zs') as [s HShapeS]. exists s. split.
    + exact (source_set_relativization_binary M carrier' h a' z' g as' zs' s
        Hh HShapeG HAS HZS HShapeS).
    + apply (proj2 (numerical_renaming_binary M h ar zr r b c n delta s Hh HShapeR)).
      exists as',zs'. auto.
  - intros h a f Hh HF IH carrier carrier' b c n delta g r HD HG HR.
    assert (Hex:exists universal,h=sr_source_quantifier universal).
    { destruct Hh as [E|E];subst h;[exists true|exists false];reflexivity. }
    destruct Hex as [universal E]. subst h.
    destruct (proj1 (numerical_renaming_quantifier M universal a f b c n delta g HF) HG)
      as [d [e [m [a' [HL [HA HShapeG]]]]]].
    destruct (source_set_relativization_quantifier_inv M carrier universal a f r HF HR)
      as [ar [HAR HShapeR]].
    destruct (IH (succM M carrier)(succM M carrier') d e m delta a' ar
      (proj2(proj2 HL) carrier carrier' HD) HA HAR) as [as' [HAS RAS]].
    destruct (ssr_quantifier_total M universal carrier' as') as [s HShapeS]. exists s. split.
    + exact (source_set_relativization_quantifier M carrier' universal a' g as' s HShapeG HAS HShapeS).
    + exact (ssr_quantifier_renaming M universal carrier carrier' ar r b c n delta d e m as' s
        HD HL HShapeR RAS HShapeS).
Qed.

Theorem source_set_relativization_renaming M carrier carrier' f r b c n delta g s :
  renaming_lookup M b c n delta carrier carrier' ->
  source_set_relativization M carrier f r -> numerical_renaming M f b c n delta g ->
  numerical_renaming M r b c n delta s -> source_set_relativization M carrier' g s.
Proof.
  intros HD HR HG HS.
  destruct (source_set_relativization_renaming_exists M f carrier carrier' b c n delta g r HD HG HR)
    as [s' [HR' HS']].
  rewrite (numerical_renaming_functional M r b c n delta s s' HS HS'). exact HR'.
Qed.

Print Assumptions source_set_relativization_renaming_exists.
Print Assumptions source_set_relativization_renaming.
