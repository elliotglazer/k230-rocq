(** An actual descriptor proof map retaining an outer local condition. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
  SourceDescriptorProvability SourceDescriptorClosure SourceConditionalUniversalMap.
Unset Implicit Arguments.

Theorem source_descriptor_conditional_universal_map M T condition shifted a b guard ab point ga gb qa qb qmap cond k :
  source_bounded M condition k ->source_formula_shift M condition shifted ->
  source_bounded M a (succM M k) ->source_bounded M b (succM M k) ->source_bounded M guard (succM M k) ->
  sf_relation M SFImpl a b ab ->sf_relation M SFImpl shifted ab point ->
  sf_relation M SFImpl guard a ga ->sf_relation M SFImpl guard b gb ->
  sf_relation M SFAll ga (zeroM M) qa ->sf_relation M SFAll gb (zeroM M) qb ->
  sf_relation M SFImpl qa qb qmap ->sf_relation M SFImpl condition qmap cond ->
  source_descriptor_provable M T point ->source_descriptor_provable M T cond.
Proof.
  intros HC HS HA HB HG HAB HP HGA HGB HQA HQB HMap HCond PP.
  destruct (sf_relation_total M SFAll point (zeroM M)) as (qpoint&HQPoint).
  destruct (sf_relation_total M SFImpl qpoint cond) as (out&HOut).
  pose proof (source_descriptor_provable_all M T point qpoint PP HQPoint) as PQ.
  pose proof (source_descriptor_provable_from_empty M T out
    (source_conditional_universal_map M condition shifted a b guard ab point qpoint ga gb qa qb qmap cond out k
      HC HS HA HB HG HAB HP HQPoint HGA HGB HQA HQB HMap HCond HOut)) as POut.
  exact (source_descriptor_provable_mp M T qpoint cond out PQ POut HOut).
Qed.

Print Assumptions source_descriptor_conditional_universal_map.
