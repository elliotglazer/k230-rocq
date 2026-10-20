(** The proved uniform least-ordinal theorem supplies the actual least
    witnesses used by the literal ordinal-collection relation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalRenaming SourceOrdinalPredicate SourceOrdinalCollectionRecipe
  SourceOrdinalCollectionLeast SourceLeastOrdinalZFR SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_oc_least_witnesses M phi oc count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  exists least leastbody inputbody inputex implication,
    numerical_renaming M oc (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) leastbody /\
    sf_relation M SFEx leastbody (zeroM M) least /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) phi inputbody /\
    sf_relation M SFEx inputbody (zeroM M) inputex /\
    sf_relation M SFImpl inputex least implication /\source_zfr_provable M implication.
Proof.
  intros HB HOC.
  destruct (source_zfr_least_ordinal_total M phi (succM M count) HB)
    as (least&inputbody&inputex&implication&HG&HInputBody&HInputEx&HImp&PImp).
  destruct (source_oc_reopened_is_least M phi oc least (succM M (succM M count)) HB HOC HG)
    as (leastbody&HSwap&HLeastEx).
  exists least,leastbody,inputbody,inputex,implication.
  split;[exact HSwap|]. split;[exact HLeastEx|]. split;[exact HInputBody|].
  split;[exact HInputEx|]. split;assumption.
Qed.

Print Assumptions source_zfr_oc_least_witnesses.
