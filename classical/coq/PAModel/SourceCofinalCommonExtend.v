(** Actual internally finite membership-block extension through a raw
    subset, preserving the same chosen new K-level as existential witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation SourceOrdinalPredicate SourceHierarchySyntax SourceRawSubset
 SourceConjunctionRules SourceInstantiationConstructors SourceCommonLevelPoint SourceCommonLevelExtendPoint
 SourceCofinalCommonPoint SourceCofinalCommonRecipe SourceCofinalCommonWitness.
Unset Implicit Arguments.
Theorem source_full_cofinal_common_extend_point M b c l start count K d y old e z target ordinal level subset last member k :
 (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->
 coding_lt M y k ->coding_lt M z k ->context_bounded M b c l k ->
 source_cofinal_common_point M start count K d y old ->
 source_cofinal_common_point M start(succM M count)K e z target ->
 numerical_instantiation M(source_ordinal_predicate_code M)e ordinal ->source_LL_instance M e z level ->
 source_raw_subset_graph M y z subset ->sf_relation M SFMember(addM M count start)z last ->
 sf_relation M SFMember e K member ->
 source_full_prv M b c l old ->source_full_prv M b c l ordinal ->source_full_prv M b c l level ->
 source_full_prv M b c l subset ->source_full_prv M b c l last ->source_full_prv M b c l member ->
 source_full_prv M b c l target.
Proof.
 intros HN HY HZ HC(oldcommon&oldmem&HOC&HOM&HOld)(newcommon&newmem&HNC&HNM&HNew)
 HO HL HS HLast HMember POld POrd PLevel PSubset PLast PMember.
 pose proof(source_full_conjunction_right M b c l oldmem oldcommon old HOld POld)as POldCommon.
 pose proof(source_full_common_level_extend_point M b c l start count d y oldcommon e z newcommon
 ordinal level subset last k HN HY HZ HC HOC HNC HO HL HS HLast POldCommon POrd PLevel PSubset PLast)as PNewCommon.
 pose proof(sf_relation_functional M SFMember e K member newmem HMember HNM)as E. subst newmem.
 exact(full_source_CI M b c l member newcommon target
 (source_wf_binary M b c l SFAnd member newcommon target(or_introl eq_refl)HNew
 (source_full_prv_wellformed M b c l member PMember)(source_full_prv_wellformed M b c l newcommon PNewCommon))
 PMember PNewCommon HNew).
Qed.
Theorem source_full_cofinal_common_extend_witness M b c l start count K d y old e z target ordinal level subset last member k :
 (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->
 coding_lt M K k ->coding_lt M y k ->coding_lt M z k ->context_bounded M b c l k ->
 source_cofinal_common_point M start count K d y old ->source_cofinal_common_recipe M start(succM M count)K target ->
 numerical_instantiation M(source_ordinal_predicate_code M)e ordinal ->source_LL_instance M e z level ->
 source_raw_subset_graph M y z subset ->sf_relation M SFMember(addM M count start)z last ->
 sf_relation M SFMember e K member ->
 source_full_prv M b c l old ->source_full_prv M b c l ordinal ->source_full_prv M b c l level ->
 source_full_prv M b c l subset ->source_full_prv M b c l last ->source_full_prv M b c l member ->
 source_full_prv M b c l target.
Proof.
 intros HN HK HY HZ HC HOld HTarget HO HL HS HLast HM POld POrd PLevel PSubset PLast PMember.
 destruct(source_cofinal_common_point_total M start(succM M count)K e z)as(point&HP).
 apply(source_full_cofinal_common_witness M b c l start(succM M count)K e z point target k HN HK HC HP HTarget).
 exact(source_full_cofinal_common_extend_point M b c l start count K d y old e z point ordinal level subset last member k
 HN HY HZ HC HOld HP HO HL HS HLast HM POld POrd PLevel PSubset PLast PMember).
Qed.
Print Assumptions source_full_cofinal_common_extend_point.
Print Assumptions source_full_cofinal_common_extend_witness.
