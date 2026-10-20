(** PA-definable induction proves that arbitrary internally many Dn steps
    preserve actual source provability of an implication. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceDn SourceDnBounds SourceDnProofStep SourceDescriptorProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_dn_proof_map_at M T count :=forall a b outA outB k implication result,
  source_bounded M a (addM M count(succM M(succM M k))) ->
  source_bounded M b (addM M count(succM M(succM M k))) ->
  source_dn M count a outA ->source_dn M count b outB ->
  sf_relation M SFImpl a b implication ->sf_relation M SFImpl outA outB result ->
  source_descriptor_provable M T implication ->source_descriptor_provable M T result.

Definition source_dn_proof_map_formula T :form :=
  ∀∀∀∀∀∀∀(source_bounded_accept_formula $6 ($7 ⊕ σ(σ $2)) →
    source_bounded_accept_formula $5 ($7 ⊕ σ(σ $2)) →
    source_dn_formula $7 $6 $4 →source_dn_formula $7 $5 $3 →
    sf_formula SFImpl $6 $5 $1 →sf_formula SFImpl $4 $3 $0 →
    source_descriptor_provable_formula T $1 →source_descriptor_provable_formula T $0).
Local Opaque holds source_bounded_accept_formula source_dn_formula sf_formula source_descriptor_provable_formula.

Lemma source_dn_proof_map_definable M T :Definable1 M(source_dn_proof_map_at M T).
Proof.
  exists(source_dn_proof_map_formula T),(fun _=>zeroM M). intro count.
  unfold source_dn_proof_map_formula,source_dn_proof_map_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite source_dn_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite source_descriptor_provable_formula_correct. reflexivity.
Qed.

Theorem source_descriptor_dn_map M T count :source_dn_proof_map_at M T count.
Proof.
  revert count. apply(definable_induction M(source_dn_proof_map_at M T)(source_dn_proof_map_definable M T)).
  - intros a b outA outB k implication result HA HB HDA HDB HI HR PI.
    apply source_dn_zero in HDA. apply source_dn_zero in HDB. subst outA outB.
    rewrite(sf_relation_functional M SFImpl a b result implication HR HI). exact PI.
  - intros count IH a b outA outB k implication result HA HB HDA HDB HI HR PI.
    apply source_dn_succ in HDA. apply source_dn_succ in HDB.
    destruct HDA as (prevA&HDA&HSA). destruct HDB as (prevB&HDB&HSB).
    assert(E:addM M(succM M count)(succM M(succM M k))=
      addM M count(succM M(succM M(succM M k)))).
    { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count(succM M(succM M(succM M k)))),
        Arithmetic.add_succ,(Arithmetic.add_comm M(succM M(succM M k)) count). reflexivity. }
    rewrite E in HA,HB.
    destruct(sf_relation_total M SFImpl prevA prevB) as (previousImp&HP).
    pose proof(IH a b prevA prevB(succM M k) implication previousImp HA HB HDA HDB HI HP PI) as PPrevious.
    exact(source_descriptor_dn_successor_map M T prevA prevB outA outB previousImp result k
      (source_dn_bounded M count a prevA(succM M k) HDA HA)
      (source_dn_bounded M count b prevB(succM M k) HDB HB) HSA HSB HP HR PPrevious).
Qed.

Print Assumptions source_dn_proof_map_definable.
Print Assumptions source_descriptor_dn_map.
