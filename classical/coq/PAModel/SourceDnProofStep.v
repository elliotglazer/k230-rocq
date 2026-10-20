(** The actual Dn successor preserves a provable implication. No transformer
    of source proofs is supplied as a premise. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalRenaming SourceDnStep SourceDescriptorProvability SourceDescriptorClosure
  SourceDescriptorUniversalMap.
Unset Implicit Arguments.

Theorem source_descriptor_dn_successor_map M T a b outA outB implication result k :
  source_bounded M a (succM M(succM M(succM M k))) ->
  source_bounded M b (succM M(succM M(succM M k))) ->
  source_dn_successor M a outA ->source_dn_successor M b outB ->
  sf_relation M SFImpl a b implication ->sf_relation M SFImpl outA outB result ->
  source_descriptor_provable M T implication ->source_descriptor_provable M T result.
Proof.
  intros HA HB (ra&guardA&pointA&HRA&HGA&HPA&HAllA)
    (rb&guardB&pointB&HRB&HGB&HPB&HAllB) HI HResult PI.
  pose proof(sf_relation_functional M SFMember _ _ guardB guardA HGB HGA) as E. subst guardB.
  destruct(sf_relation_total M SFImpl ra rb) as (rotated&HRot).
  assert(HRen:numerical_renaming M implication (code_numeral M 1653)(code_numeral M 6)
    (code_numeral M 3)(zeroM M) rotated).
  { apply(proj2(numerical_renaming_binary M SFImpl a b implication _ _ _ _ rotated
      (or_intror(or_intror eq_refl)) HI)). exists ra,rb. repeat split;assumption. }
  pose proof(source_descriptor_provable_renaming M T implication _ _ _ _ rotated PI HRen) as PRot.
  pose proof(source_dn_rotate_bounded M a ra k HA HRA) as HRA0.
  pose proof(source_dn_rotate_bounded M b rb k HB HRB) as HRB0.
  assert(HGuard:source_bounded M guardA (succM M(succM M(succM M k)))).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ guardA _ (or_introl eq_refl) HGA)).
    split;[apply coding_zero_lt_succ|]. apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
  destruct(sf_relation_total M SFImpl pointA pointB) as (pointMap&HPointMap).
  pose proof(source_descriptor_implication_guard M T guardA ra rb rotated pointA pointB pointMap
    (succM M(succM M(succM M k))) HGuard HRA0 HRB0 HRot HPA HPB HPointMap PRot) as PPoint.
  assert(HPointA:source_bounded M pointA (succM M(succM M(succM M k)))).
  { exact(proj2(source_bounded_accept_binary M SFImpl guardA ra pointA _
      (or_intror(or_intror eq_refl)) HPA)(conj HGuard HRA0)). }
  assert(HPointB:source_bounded M pointB (succM M(succM M(succM M k)))).
  { exact(proj2(source_bounded_accept_binary M SFImpl guardA rb pointB _
      (or_intror(or_intror eq_refl)) HPB)(conj HGuard HRB0)). }
  exact(source_descriptor_universal_map M T pointA pointB pointMap outA outB result
    (succM M(succM M(succM M k))) HPointA HPointB HPointMap HAllA HAllB HResult PPoint).
Qed.

Print Assumptions source_descriptor_dn_successor_map.
