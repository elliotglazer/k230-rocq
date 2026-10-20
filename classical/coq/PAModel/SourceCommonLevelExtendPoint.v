(** The substantive successor step for the parameter table: transport the
    old members through the actual subset law, append the new member, and
    choose the new ordinal and level as the same two existential witnesses. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull SourceInstantiationConstructors SourceConjunctionRules
  SourceMembershipBlocks SourceMembershipBlockProofs SourceMembershipBlockMonotone SourceRawSubset
  SourceCommonLevelPoint SourceCommonLevelRecipe SourceCommonLevelWitness SourceHierarchySyntax
  SourceOrdinalPredicate NumericalInstantiation.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_full_common_level_extend_point M b c l start count d y old e z target ordinal level subset last k :
  (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->
  coding_lt M y k ->coding_lt M z k ->context_bounded M b c l k ->
  source_common_level_point M start count d y old ->
  source_common_level_point M start(succM M count)e z target ->
  numerical_instantiation M(source_ordinal_predicate_code M)e ordinal ->source_LL_instance M e z level ->
  source_raw_subset_graph M y z subset ->sf_relation M SFMember(addM M count start)z last ->
  source_full_prv M b c l old ->source_full_prv M b c l ordinal ->source_full_prv M b c l level ->
  source_full_prv M b c l subset ->source_full_prv M b c l last ->source_full_prv M b c l target.
Proof.
  intros HNames HY HZ HC (members&od&ld&pair&HM&HOD&HLD&HP&HF)
    (members'&oe&le&pair'&HM'&HOE&HLE&HP'&HF') HOrd HLevel HSubset HLast
    POld POrdinal PLevel PSubset PLast.
  pose proof(numerical_instantiation_functional M _ e ordinal oe HOrd HOE) as E. subst oe.
  pose proof(source_LL_instance_functional M e z level le HLevel HLE) as E. subst le.
  pose proof(source_full_conjunction_right M b c l pair members old HF POld) as PMembers.
  apply source_membership_block_succ in HM'.
  destruct HM' as(prefix&last'&HPrefix&HLast'&HAnd).
  pose proof(sf_relation_functional M SFMember(addM M count start)z last last' HLast HLast') as E. subst last'.
  assert(HNamesPrefix:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
  { intros i HI. exact(HNames i(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count))). }
  pose proof(source_full_membership_block_monotone M start y z count members prefix subset b c l k
    HNamesPrefix HY HZ HM HPrefix HSubset HC PMembers PSubset) as PPrefix.
  pose proof(full_source_CI M b c l prefix last members'
    (source_wf_binary M b c l SFAnd prefix last members'(or_introl eq_refl)HAnd
      (source_full_prv_wellformed M b c l prefix PPrefix)(source_full_prv_wellformed M b c l last PLast))
    PPrefix PLast HAnd) as PMembers'.
  pose proof(full_source_CI M b c l ordinal level pair'
    (source_wf_binary M b c l SFAnd ordinal level pair'(or_introl eq_refl)HP'
      (source_full_prv_wellformed M b c l ordinal POrdinal)(source_full_prv_wellformed M b c l level PLevel))
    POrdinal PLevel HP') as PPair'.
  exact(full_source_CI M b c l pair' members' target
    (source_wf_binary M b c l SFAnd pair' members' target(or_introl eq_refl)HF'
      (source_full_prv_wellformed M b c l pair' PPair')(source_full_prv_wellformed M b c l members' PMembers'))
    PPair' PMembers' HF').
Qed.

Theorem source_full_common_level_extend_witness M b c l start count d y old e z target ordinal level subset last k :
  (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->
  coding_lt M y k ->coding_lt M z k ->context_bounded M b c l k ->
  source_common_level_point M start count d y old ->source_common_level_recipe M start(succM M count)target ->
  numerical_instantiation M(source_ordinal_predicate_code M)e ordinal ->source_LL_instance M e z level ->
  source_raw_subset_graph M y z subset ->sf_relation M SFMember(addM M count start)z last ->
  source_full_prv M b c l old ->source_full_prv M b c l ordinal ->source_full_prv M b c l level ->
  source_full_prv M b c l subset ->source_full_prv M b c l last ->source_full_prv M b c l target.
Proof.
  intros HNames HY HZ HC HOld HTarget HOrd HLevel HSubset HLast POld POrdinal PLevel PSubset PLast.
  destruct(source_common_level_point_total M start(succM M count)e z) as(point&HPoint).
  apply(source_full_common_level_witness M b c l start(succM M count)e z point target k HNames HC HPoint HTarget).
  exact(source_full_common_level_extend_point M b c l start count d y old e z point ordinal level subset last k
    HNames HY HZ HC HOld HPoint HOrd HLevel HSubset HLast POld POrdinal PLevel PSubset PLast).
Qed.
Print Assumptions source_full_common_level_extend_point.
Print Assumptions source_full_common_level_extend_witness.
