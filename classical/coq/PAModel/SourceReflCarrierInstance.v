(** Instantiate the hierarchy carrier in the literal Refl shell. The
    arbitrary reflected matrix stays fixed below its internal count. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationSubstitution
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceSubstitutionIdentity
  SourceHierarchySyntax SourceIffGraphs SourceBallS SourceBallSSubstitution SourceInternalLifts SourceInternalLiftLaws.
Unset Implicit Arguments.
Theorem source_refl_carrier_instance M domain count phi d left right equiv block level point y level':
  source_bounded M domain(code_numeral M 1)->source_bounded M phi count->
  source_relativization M domain phi left->source_set_relativization M count phi right->
  source_iff_graph M left right equiv->source_ballS M count(zeroM M)equiv block->
  source_LL_instance M(succM M d)(zeroM M)level->sf_relation M SFImpl level block point->
  source_LL_instance M d y level'->
  exists right1 equiv1 block1 point1,
    source_set_relativization M(addM M count y)phi right1 /\source_iff_graph M left right1 equiv1 /\
    source_ballS M count y equiv1 block1 /\sf_relation M SFImpl level' block1 point1 /\numerical_instantiation M point y point1.
Proof.
  intros HD HP HL HR HE HB HLevel HPoint HLevel'.
  destruct(substitution_singleton_total M y)as(ib&ic&HHead&HTail).
  destruct(source_upn_map_total M count ib ic(code_numeral M 1)(zeroM M))as(ub&uc&HUpn).
  assert(HFix:substitution_fixes_bound M ub uc(addM M count(code_numeral M 1))(addM M count(zeroM M))count).
  { intros i HI. exact(source_upn_map_head M count ib ic(code_numeral M 1)(zeroM M)ub uc i HUpn HI). }
  pose proof(numerical_substitution_identity_on_bound M phi ub uc(addM M count(code_numeral M 1))
    (addM M count(zeroM M))count HP HFix)as HPhi.
  pose proof(source_relativization_preserves_bound M phi domain count left HD HP HL)as BLeft.
  pose proof(numerical_substitution_identity_on_bound M left ub uc(addM M count(code_numeral M 1))
    (addM M count(zeroM M))count BLeft HFix)as HLeft.
  pose proof(source_upn_map_tail M count ib ic(code_numeral M 1)(zeroM M)ub uc(zeroM M)y HUpn HHead)as HCarrier.
  rewrite coding_add_zero_r in HCarrier.
  assert(HCarrier':substitution_lookup M ub uc(addM M count(code_numeral M 1))(addM M count(zeroM M))count(addM M count y)).
  { now rewrite coding_add_zero_r. }
  destruct(source_set_relativization_substitution_exists M phi count(addM M count y)ub uc
    (addM M count(code_numeral M 1))(addM M count(zeroM M))phi right HCarrier' HPhi HR)
    as(right1&HR1&HRight).
  destruct(source_iff_total M left right1)as(equiv1&HE1).
  pose proof(source_iff_substitution M left right equiv left right1 equiv1 ub uc
    (addM M count(code_numeral M 1))(addM M count(zeroM M))HE HE1 HLeft HRight)as HEquiv.
  destruct(numerical_substitution_total M block ib ic(code_numeral M 1)(zeroM M))as(block1&HBlock).
  pose proof(source_ballS_substitution M count(zeroM M)equiv block ib ic(code_numeral M 1)(zeroM M)y equiv1 block1 ub uc
    HHead HB HUpn HEquiv HBlock)as HB1.
  pose proof(source_LL_instance_substitution M(succM M d)(zeroM M)level d y level' ib ic(code_numeral M 1)(zeroM M)
    HLevel HLevel'(substitution_singleton_tail M ib ic d)HHead)as HLevelSub.
  destruct(sf_relation_total M SFImpl level' block1)as(point1&HPoint1).
  assert(HPointSub:numerical_substitution M point ib ic(code_numeral M 1)(zeroM M)point1).
  { apply(proj2(numerical_substitution_binary M SFImpl level block point ib ic(code_numeral M 1)(zeroM M)point1
      (or_intror(or_intror eq_refl))HPoint)). exists level',block1. auto. }
  exists right1,equiv1,block1,point1. split;[exact HR1|]. split;[exact HE1|]. split;[exact HB1|].
  split;[exact HPoint1|]. exists ib,ic. auto.
Qed.
Print Assumptions source_refl_carrier_instance.
