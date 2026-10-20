(** PA-definable induction over the actual internal parameter count. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceDn SourceDnBounds SourceDnCarrierStep SourceDescriptorProvability SourceZFRProvability
  SourceQuantifierRules SourceFiniteCutoffShift SourceQfFunctionality SourceDnCutoffDiamonds NumericalRenaming.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_dn_carrier_map_at M count :=
  forall condition body pa pb dn da db k baseMap base resultMap result,
    sf_relation M SFEqual(code_numeral M 1)(code_numeral M 2)condition ->
    source_bounded M body(addM M count(succM M(succM M k))) ->
    source_dn M count body dn ->
    source_cutoff_shift M 2 body pa ->source_cutoff_shift M 1 body pb ->
    source_cutoff_shift M 2 dn da ->source_cutoff_shift M 1 dn db ->
    sf_relation M SFImpl pa pb baseMap ->sf_relation M SFImpl condition baseMap base ->
    sf_relation M SFImpl da db resultMap ->sf_relation M SFImpl condition resultMap result ->
    source_zfr_provable M base ->source_zfr_provable M result.

Definition source_dn_carrier_map_formula :form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀ (
    sf_formula SFEqual(num 1)(num 2)$11 →
    source_bounded_accept_formula $10($12 ⊕ σ(σ $4)) →
    source_dn_formula $12 $10 $7 →
    source_cutoff_shift_formula 2 $10 $9 →source_cutoff_shift_formula 1 $10 $8 →
    source_cutoff_shift_formula 2 $7 $6 →source_cutoff_shift_formula 1 $7 $5 →
    sf_formula SFImpl $9 $8 $3 →sf_formula SFImpl $11 $3 $2 →
    sf_formula SFImpl $6 $5 $1 →sf_formula SFImpl $11 $1 $0 →
    source_zfr_provable_formula $2 →source_zfr_provable_formula $0).
Local Opaque holds source_bounded_accept_formula source_dn_formula source_formula_shift_formula
  source_cutoff_shift_formula sf_formula source_zfr_provable_formula.

Lemma source_dn_carrier_map_definable M :Definable1 M(source_dn_carrier_map_at M).
Proof.
  exists(source_dn_carrier_map_formula),(fun _=>zeroM M). intro count.
  unfold source_dn_carrier_map_formula,source_dn_carrier_map_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite source_dn_formula_correct.
  setoid_rewrite source_cutoff_shift_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite source_zfr_provable_formula_correct. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Theorem source_zfr_dn_carrier_map M count :source_dn_carrier_map_at M count.
Proof.
  revert count. apply(definable_induction M(source_dn_carrier_map_at M)(source_dn_carrier_map_definable M)).
  - intros condition body pa pb dn da db k baseMap base resultMap result HC HB HD HPA HPB HDA HDB HBM HB0 HRM HR0 PB.
    apply source_dn_zero in HD. subst dn.
    assert(EA:da=pa) by(eapply source_cutoff_shift_functional;[exact HDA|exact HPA]). subst da.
    assert(EB:db=pb) by(eapply source_cutoff_shift_functional;[exact HDB|exact HPB]). subst db.
    assert(EM:resultMap=baseMap) by(eapply sf_relation_functional;[exact HRM|exact HBM]). subst resultMap.
    rewrite(sf_relation_functional M SFImpl condition baseMap result base HR0 HB0). exact PB.
  - intros count IH condition body pa pb dn da db k baseMap base resultMap result HC HB HD HPA HPB HDA HDB HBM HB0 HRM HR0 PB.
    apply source_dn_succ in HD. destruct HD as(prev&HD&HStep).
    assert(E:addM M(succM M count)(succM M(succM M k))=
      addM M count(succM M(succM M(succM M k)))).
    { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count(succM M(succM M(succM M k)))),
        Arithmetic.add_succ,(Arithmetic.add_comm M(succM M(succM M k)) count). reflexivity. }
    rewrite E in HB.
    destruct(source_cutoff_shift_total M 2 prev) as(prevA&HPrevA).
    destruct(source_cutoff_shift_total M 1 prev) as(prevB&HPrevB).
    destruct(sf_relation_total M SFImpl prevA prevB) as(previousMap&HPreviousMap).
    destruct(sf_relation_total M SFImpl condition previousMap) as(previous&HPrevious).
    pose proof(IH condition body pa pb prev prevA prevB(succM M k) baseMap base previousMap previous
      HC HB HD HPA HPB HPrevA HPrevB HBM HB0 HPreviousMap HPrevious PB) as PPrevious.
    exact(source_zfr_dn_carrier_step M condition prev dn prevA prevB da db previousMap previous resultMap result k
      HC(source_dn_bounded M count body prev(succM M k) HD HB) HStep HPrevA HPrevB HDA HDB
      HPreviousMap HPrevious HRM HR0 PPrevious).
Qed.

Print Assumptions source_dn_carrier_map_definable.
Print Assumptions source_zfr_dn_carrier_map.
