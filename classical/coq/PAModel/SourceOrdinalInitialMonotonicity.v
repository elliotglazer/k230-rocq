(** Initial monotonicity in the X0/parameter1 context. Its actual source shift is the generic collector-context formula. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalInstantiation NumericalRenaming RenamingSubstitution NumericalSubstitutionMaps NumericalSubstitution
  SourceFiniteCutoffShift SourceCutoffQuantifiers SourceOrdinalInitialMonoMaps
  SourceOrdinalMonotoneUse SourceOrdinalMonotoneMaps SourceOrdinalPredicate SourceDomainInstances
  SourceSubstitutionIdentity SourceSubsetSubstitution SourcePropositionalSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_oc_initial_monotonicity_graph M phi mono :=exists left right ordD subset point inner middle,
  source_oc_initial_mono_matrix M false phi left /\source_oc_initial_mono_matrix M true phi right /\
  numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1) ordD /\
  SourceOrdinalUpperMembers.source_oc_subset_graph M(code_numeral M 1)(zeroM M) subset /\
  code_relation M(source_oc_mono_environment ordD(source_ordinal_predicate_code M) subset left right)
    (SourcePropositionalTemplates.source_prop_expression source_oc_mono_template) point /\
  sf_relation M SFAll point(zeroM M) inner /\sf_relation M SFAll inner(zeroM M) middle /\
  sf_relation M SFAll middle(zeroM M) mono.

Theorem source_oc_initial_monotonicity_shift M phi mono mono' k :
  source_bounded M phi k ->source_oc_initial_monotonicity_graph M phi mono ->
  SourceQuantifierRules.source_formula_shift M mono mono' ->source_oc_monotonicity_graph M phi mono'.
Proof.
  intros HB (left&right&ordD&subset&point&inner&middle&HL&HR&HD&HS&HP&HI&HM&HO) HShift.
  assert(HC0:source_cutoff_shift M 0 mono mono').
  { exists(zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    apply(proj1(numerical_renaming_substitution M mono(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) mono')) in HShift.
    rewrite Arithmetic.add_zero in HShift. exact HShift. }
  destruct(source_cutoff_quantifier_inv M 0 true middle mono mono' HO HC0) as (middle'&HO'&HC1).
  destruct(source_cutoff_quantifier_inv M 1 true inner middle middle' HM HC1) as (inner'&HM'&HC2).
  destruct(source_cutoff_quantifier_inv M 2 true point inner inner' HI HC2) as (point'&HI'&sb&sc&sn&HMap&HPoint).
  destruct(numerical_substitution_total M left sb sc sn(code_numeral M 4)) as (left'&HLeft).
  destruct(numerical_substitution_total M right sb sc sn(code_numeral M 4)) as (right'&HRight).
  assert(HL':source_oc_mono_matrix M false phi left').
  { apply(source_oc_initial_mono_matrix_shift M false phi left left' k HB HL).
    exists sb,sc,sn. split;assumption. }
  assert(HR':source_oc_mono_matrix M true phi right').
  { apply(source_oc_initial_mono_matrix_shift M true phi right right' k HB HR).
    exists sb,sc,sn. split;assumption. }
  assert(HFix:forall f,source_bounded M f(code_numeral M 2) ->
    numerical_substitution M f sb sc sn(code_numeral M 4) f).
  { intros f HF. apply(numerical_substitution_identity_on_bound M f sb sc sn(code_numeral M 4)(code_numeral M 2) HF).
    intros i HBound. destruct(SourceNumeralLift.source_numeral_initial_segment M 2 i HBound) as (j&HJ&->).
    destruct j as [|[|j]];try lia.
    - exact(source_cutoff_shift_map_fixed_lookup M 3 sb sc sn HMap 0).
    - exact(source_cutoff_shift_map_fixed_lookup M 3 sb sc sn HMap 1). }
  assert(HOrdD:numerical_substitution M ordD sb sc sn(code_numeral M 4) ordD).
  { apply HFix. exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1) ordD
      (code_numeral M 2)(source_ordinal_predicate_bounded M)(coding_lt_succ M(code_numeral M 1)) HD). }
  assert(HOrd:numerical_substitution M(source_ordinal_predicate_code M) sb sc sn(code_numeral M 4)
    (source_ordinal_predicate_code M)).
  { apply(numerical_substitution_identity_on_bound M _ sb sc sn(code_numeral M 4)(code_numeral M 1)
      (source_ordinal_predicate_bounded M)). intros i HBound. rewrite(domain_index_below_one M i HBound).
    exact(source_cutoff_shift_map_fixed_lookup M 3 sb sc sn HMap 0). }
  pose proof(source_oc_subset_substitution M(code_numeral M 1)(zeroM M) subset(code_numeral M 1)(zeroM M) subset
    sb sc sn(code_numeral M 4) HS
    (source_cutoff_shift_map_fixed_lookup M 3 sb sc sn HMap 1)
    (source_cutoff_shift_map_fixed_lookup M 3 sb sc sn HMap 0) HS) as HSubset.
  destruct(code_relation_total M(SourcePropositionalTemplates.source_prop_expression source_oc_mono_template)
    (source_oc_mono_environment ordD(source_ordinal_predicate_code M) subset left' right')) as (newPoint&HNewPoint).
  assert(HNew:numerical_substitution M point sb sc sn(code_numeral M 4) newPoint).
  { apply(source_prop_expression_substitution M
      (source_oc_mono_environment ordD(source_ordinal_predicate_code M) subset left right)
      (source_oc_mono_environment ordD(source_ordinal_predicate_code M) subset left' right')
      sb sc sn(code_numeral M 4) source_oc_mono_template);[|exact HP|exact HNewPoint].
    intros [|[|[|[|i]]]];cbn [source_oc_mono_environment];assumption. }
  pose proof(numerical_substitution_functional M point sb sc sn(code_numeral M 4) point' newPoint HPoint HNew) as E.
  subst point'.
  exists left',right',ordD,subset,newPoint,inner',middle'. repeat split;assumption.
Qed.

Print Assumptions source_oc_initial_monotonicity_shift.
