(** The literal ordinal-collection relation, reopened in output/input
    order, is exactly the canonical least-ordinal matrix. This identity
    holds for arbitrary internally coded predicates and bounds. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalInstantiation NumericalRenamingMaps NumericalRenaming
  SourceSwap SourceFixedSwap SourceDomainInstances SourceOrdinalPredicate
  SourceOrdinalCollectionRecipe SourceOrdinalCollectionMaps SourceLeastOrdinalGoal
  SourceLeastOrdinalShift SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_oc_reopened_is_least M phi oc least k :
  source_bounded M phi k ->source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  source_least_ordinal_graph M phi least ->
  exists body,
    numerical_renaming M oc (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) body /\sf_relation M SFEx body (zeroM M) least.
Proof.
  intros HB (ord1&swapped&tail&inner&HOrd1&HSwapped&HTail&HInner&HOC) (inserted&HInserted&HLeast).
  destruct (source_least_ordinal_expression_split M phi inserted least HLeast)
    as (body&tag&allpoint&point&negphi&mem01&HEx&HBody&HTag&HAll&HPoint&HMem01&HNegPhi).
  destruct (numerical_renaming_total M ord1 (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M)) as (ord0&ROrd).
  pose proof (source_collection_domain_instance_renaming M (source_ordinal_predicate_code M)
    (code_numeral M 1) ord1 (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) ord0 (zeroM M)
    (source_ordinal_predicate_bounded M) HOrd1 ROrd (proj2 (source_fixed_swap_map M))) as HOrd0.
  pose proof (numerical_instantiation_functional M _ (zeroM M) ord0 (source_ordinal_predicate_code M)
    HOrd0 (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))) as EOrd. subst ord0.
  destruct (numerical_renaming_total M swapped (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M)) as (phi'&RPhi).
  pose proof (source_fixed_swap_twice M phi swapped phi' k HB HSwapped RPhi) as EPhi. subst phi'.
  destruct HTail as (shifted&mem02&neg&tailpoint&HShifted&HMem02&HNeg&HTailPoint&HTailAll).
  destruct (renaming_lift_total M (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M)) as (rb&rc&rn&HL).
  destruct (numerical_renaming_total M shifted rb rc rn (zeroM M)) as (shifted'&RShifted).
  pose proof (source_cutoff_two_lifted_swap M phi shifted shifted' inserted k rb rc rn
    HB HShifted HL RShifted HInserted) as EShifted. subst shifted'.
  assert (RMem:numerical_renaming M mem02 rb rc rn (zeroM M) mem01).
  { apply (proj2 (numerical_renaming_member M (zeroM M) (code_numeral M 2) mem02
      rb rc rn (zeroM M) mem01 HMem02)).
    exists (zeroM M),(code_numeral M 1). split;[exact (proj1 (proj2 HL))|].
    split;[|exact HMem01]. exact (proj2 (proj2 HL) (code_numeral M 1) (zeroM M)
      (proj2 (source_fixed_swap_map M))). }
  assert (RFalse:numerical_renaming M (zeroM M) rb rc rn (zeroM M) (zeroM M)).
  { apply (proj2 (numerical_renaming_invalid M (zeroM M) rb rc rn (zeroM M) (zeroM M)
      (or_introl eq_refl))). reflexivity. }
  assert (RNeg:numerical_renaming M neg rb rc rn (zeroM M) negphi).
  { apply (proj2 (numerical_renaming_binary M SFImpl shifted (zeroM M) neg rb rc rn (zeroM M)
      negphi (or_intror (or_intror eq_refl)) HNeg)).
    exists inserted,(zeroM M). repeat split;assumption. }
  assert (RPoint:numerical_renaming M tailpoint rb rc rn (zeroM M) point).
  { apply (proj2 (numerical_renaming_binary M SFImpl mem02 neg tailpoint rb rc rn (zeroM M)
      point (or_intror (or_intror eq_refl)) HTailPoint)).
    exists mem01,negphi. repeat split;assumption. }
  assert (RTail:numerical_renaming M tail (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) allpoint).
  { apply (proj2 (numerical_renaming_quantifier M true tailpoint tail
      (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) allpoint HTailAll)).
    exists rb,rc,rn,point. split;[exact HL|]. split;assumption. }
  assert (RInner:numerical_renaming M inner (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) tag).
  { apply (proj2 (numerical_renaming_binary M SFAnd ord1 swapped inner
      (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) tag
      (or_introl eq_refl) HInner)).
    exists (source_ordinal_predicate_code M),phi. repeat split;assumption. }
  exists body. split;[|exact HEx].
  apply (proj2 (numerical_renaming_binary M SFAnd inner tail oc
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) body
    (or_introl eq_refl) HOC)).
  exists tag,allpoint. repeat split;assumption.
Qed.

Print Assumptions source_oc_reopened_is_least.
