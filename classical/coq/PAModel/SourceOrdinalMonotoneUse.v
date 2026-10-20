(** Actual three-quantifier monotonicity specialization for arbitrary
    internally coded predicates. All matrix substitutions are normalized. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalSubstitution NumericalSubstitutionMaps NumericalInstantiation
  NumericalSourceFull SourceDerivedRules SourceOrdinalPredicate SourceDomainInstances
  SourceUnarySubstitution SourceSubsetSubstitution SourceOrdinalUpperMembers
  SourceTripleSpecialization SourceOrdinalMonotoneMaps SourceRoleReopening
  SourcePropositionalTemplates SourcePropositionalSubstitution SourceFunctionalityShells.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_oc_mono_environment {A} (ordD ordU subset left right:A) i :=
  match i with 0=>ordD|1=>ordU|2=>subset|3=>left|_=>right end.
Definition source_oc_mono_template :=SPTImpl (SPTSlot 0)
  (SPTImpl (SPTSlot 1) (SPTImpl (SPTSlot 2) (SPTImpl (SPTSlot 3) (SPTSlot 4)))).
Definition source_oc_monotonicity_graph M phi mono :=exists left right ordD subset point inner middle,
  source_oc_mono_matrix M false phi left /\source_oc_mono_matrix M true phi right /\
  numerical_instantiation M (source_ordinal_predicate_code M) (code_numeral M 1) ordD /\
  source_oc_subset_graph M (code_numeral M 1) (zeroM M) subset /\
  code_relation M (source_oc_mono_environment ordD (source_ordinal_predicate_code M) subset left right)
    (source_prop_expression source_oc_mono_template) point /\
  sf_relation M SFAll point (zeroM M) inner /\sf_relation M SFAll inner (zeroM M) middle /\
  sf_relation M SFAll middle (zeroM M) mono.

Theorem source_full_oc_monotonicity_use M b c n phi mono k u d v db dc ub uc qd qu ordD ordU subset :
  source_bounded M phi k ->source_oc_monotonicity_graph M phi mono ->
  source_role_reopening M v d db dc ->
  numerical_substitution M phi db dc (code_numeral M 2) (code_numeral M 2) qd ->
  source_role_reopening M v u ub uc ->
  numerical_substitution M phi ub uc (code_numeral M 2) (code_numeral M 2) qu ->
  numerical_instantiation M (source_ordinal_predicate_code M) d ordD ->
  numerical_instantiation M (source_ordinal_predicate_code M) u ordU ->
  source_oc_subset_graph M d u subset ->
  source_full_prv M b c n mono ->source_full_prv M b c n ordD ->source_full_prv M b c n ordU ->
  source_full_prv M b c n subset ->source_full_prv M b c n qd ->source_full_prv M b c n qu.
Proof.
  intros HB (left&right&rawD&rawSub&point&inner&middle&HL&HR&HD&HS&HP&HI&HM&HO)
    HRoleD HQD HRoleU HQU HOrdD HOrdU HSubset PMono PD PU PS PQ.
  destruct (source_triple_prefix_total M u d v) as (tb&tc&HTriple).
  pose proof (source_oc_mono_matrix_specialization M false phi left u d v tb tc db dc qd k
    HB HL HTriple HRoleD HQD) as HDLeft.
  pose proof (source_oc_mono_matrix_specialization M true phi right u d v tb tc ub uc qu k
    HB HR HTriple HRoleU HQU) as HDRight.
  pose proof (source_domain_instance_substitution_graph M (source_ordinal_predicate_code M)
    (code_numeral M 1) rawD tb tc (code_numeral M 3) (zeroM M) d ordD
    (source_ordinal_predicate_bounded M) HD (proj1 (proj2 HTriple)) HOrdD) as HSD.
  pose proof (source_domain_instance_substitution_graph M (source_ordinal_predicate_code M)
    (zeroM M) (source_ordinal_predicate_code M) tb tc (code_numeral M 3) (zeroM M) u ordU
    (source_ordinal_predicate_bounded M)
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M)) (proj1 HTriple) HOrdU) as HSU.
  pose proof (source_oc_subset_substitution M (code_numeral M 1) (zeroM M) rawSub d u subset
    tb tc (code_numeral M 3) (zeroM M) HS (proj1 (proj2 HTriple)) (proj1 HTriple) HSubset) as HSS.
  destruct (sf_relation_total M SFImpl qd qu) as (step3&H3).
  destruct (sf_relation_total M SFImpl subset step3) as (step2&H2).
  destruct (sf_relation_total M SFImpl ordU step2) as (step1&H1).
  destruct (sf_relation_total M SFImpl ordD step1) as (instance&HInstance).
  assert (HInstanceGraph:code_relation M (source_oc_mono_environment ordD ordU subset qd qu)
    (source_prop_expression source_oc_mono_template) instance).
  { unfold source_oc_mono_template,source_prop_expression. functionality_graph. }
  assert (HSub:numerical_substitution M point tb tc (code_numeral M 3) (zeroM M) instance).
  { apply (source_prop_expression_substitution M
      (source_oc_mono_environment rawD (source_ordinal_predicate_code M) rawSub left right)
      (source_oc_mono_environment ordD ordU subset qd qu) tb tc (code_numeral M 3) (zeroM M)
      source_oc_mono_template);[|exact HP|exact HInstanceGraph].
    intros [|[|[|[|i]]]];cbn [source_oc_mono_environment];assumption. }
  destruct (source_full_prv_wellformed M b c n mono PMono) as (bound&HMonoBound&_).
  pose proof (proj1 (source_bounded_accept_unary M SFAll middle mono bound
    (or_introl eq_refl) HO) HMonoBound) as HMiddleBound.
  pose proof (proj1 (source_bounded_accept_unary M SFAll inner middle (succM M bound)
    (or_introl eq_refl) HM) HMiddleBound) as HInnerBound.
  pose proof (proj1 (source_bounded_accept_unary M SFAll point inner (succM M (succM M bound))
    (or_introl eq_refl) HI) HInnerBound) as HPointBound.
  pose proof (source_full_triple_specialize M b c n point inner middle mono v d u tb tc instance
    (succM M (succM M (succM M bound))) HPointBound HI HM HO HTriple HSub PMono) as PInstance.
  pose proof (source_full_modus_ponens M b c n ordD step1 instance HInstance PInstance PD) as P1.
  pose proof (source_full_modus_ponens M b c n ordU step2 step1 H1 P1 PU) as P2.
  pose proof (source_full_modus_ponens M b c n subset step3 step2 H2 P2 PS) as P3.
  exact (source_full_modus_ponens M b c n qd qu step3 H3 P3 PQ).
Qed.

Print Assumptions source_full_oc_monotonicity_use.
