(** Exact normalization of the internally instantiated three-quantifier
    monotonicity hypothesis in ordinal collection. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceSubstitutionIdentity
  SourceCBMonotoneMaps SourceOrdinalInitialMonotonicity SourceOrdinalMonotoneUse SourceOrdinalMonotoneMaps
  SourceOrdinalPredicate SourceOrdinalUpperMembers SourceDomainInstances SourceSubsetSubstitution
  SourcePropositionalSubstitution SourcePropositionalTemplates SourceNumeralLift.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_cb_monotonicity_graph M q out:=exists left right ordD subset point inner middle,
  source_cb_mono_matrix M false q left /\source_cb_mono_matrix M true q right /\
  numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1)ordD /\
  source_oc_subset_graph M(code_numeral M 1)(zeroM M)subset /\
  code_relation M(source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left right)
    (source_prop_expression source_oc_mono_template)point /\
  sf_relation M SFAll point(zeroM M)inner /\sf_relation M SFAll inner(zeroM M)middle /\
  sf_relation M SFAll middle(zeroM M)out.

Theorem source_cb_initial_monotonicity_instance M q old out k:
  source_bounded M q k ->source_oc_initial_monotonicity_graph M q old ->
  numerical_instantiation M old(zeroM M)out ->source_cb_monotonicity_graph M q out.
Proof.
  intros HB(left&right&ordD&subset&point&inner&middle&HL&HR&HD&HS&HP&HI&HM&HO)(b&c&HHead&HSub).
  destruct(proj1(numerical_substitution_quantifier M true middle old b c(code_numeral M 1)(zeroM M)out HO)HSub)
    as(ab&ac&an&middle'&H1&HSubMiddle&HO').
  destruct(proj1(numerical_substitution_quantifier M true inner middle ab ac an(code_numeral M 1)middle' HM)HSubMiddle)
    as(tb&tc&tn&inner'&H2&HSubInner&HM').
  destruct(proj1(numerical_substitution_quantifier M true point inner tb tc tn(code_numeral M 2)inner' HI)HSubInner)
    as(rb&rc&rn&point'&H3&HSubPoint&HI').
  assert(HMap:source_cb_collapse_three M rb rc rn).
  { exists b,c,ab,ac,an,tb,tc,tn. auto. }
  destruct(numerical_substitution_total M left rb rc rn(code_numeral M 3)) as(left'&HLeft).
  destruct(numerical_substitution_total M right rb rc rn(code_numeral M 3)) as(right'&HRight).
  pose proof(source_cb_initial_mono_matrix_collapse M false q left rb rc rn left' k HB HL HMap HLeft) as HLeft'.
  pose proof(source_cb_initial_mono_matrix_collapse M true q right rb rc rn right' k HB HR HMap HRight) as HRight'.
  assert(HFix:forall f,source_bounded M f(code_numeral M 2) ->
      numerical_substitution M f rb rc rn(code_numeral M 3)f).
  { intros f HF. apply(numerical_substitution_identity_on_bound M f rb rc rn(code_numeral M 3)(code_numeral M 2)HF).
    intros i HBound. destruct(source_numeral_initial_segment M 2 i HBound) as(j&HJ&->).
    destruct j as[|[|j]];try lia;apply(source_cb_collapse_three_head M rb rc rn _ HMap);lia. }
  assert(HOrdD:numerical_substitution M ordD rb rc rn(code_numeral M 3)ordD).
  { apply HFix. exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1)
      ordD(code_numeral M 2)(source_ordinal_predicate_bounded M)(coding_lt_succ M(code_numeral M 1))HD). }
  assert(HOrd:numerical_substitution M(source_ordinal_predicate_code M)rb rc rn(code_numeral M 3)
      (source_ordinal_predicate_code M)).
  { apply HFix. exact(SourceRelativizationBounds.sr_domain_bound_succ M(source_ordinal_predicate_code M)
      (code_numeral M 1)(source_ordinal_predicate_bounded M)). }
  pose proof(source_oc_subset_substitution M(code_numeral M 1)(zeroM M)subset(code_numeral M 1)(zeroM M)subset
    rb rc rn(code_numeral M 3)HS
    (source_cb_collapse_three_head M rb rc rn 1 HMap ltac:(lia))
    (source_cb_collapse_three_head M rb rc rn 0 HMap ltac:(lia))HS) as HSubset.
  destruct(code_relation_total M(source_prop_expression source_oc_mono_template)
    (source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left' right')) as(newPoint&HNewPoint).
  assert(HNew:numerical_substitution M point rb rc rn(code_numeral M 3)newPoint).
  { apply(source_prop_expression_substitution M
      (source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left right)
      (source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left' right')
      rb rc rn(code_numeral M 3)source_oc_mono_template);[|exact HP|exact HNewPoint].
    intros[|[|[|[|i]]]];cbn[source_oc_mono_environment];assumption. }
  pose proof(numerical_substitution_functional M point rb rc rn(code_numeral M 3)point' newPoint HSubPoint HNew) as E.
  subst point'. exists left',right',ordD,subset,newPoint,inner',middle'. repeat split;assumption.
Qed.

Print Assumptions source_cb_initial_monotonicity_instance.
