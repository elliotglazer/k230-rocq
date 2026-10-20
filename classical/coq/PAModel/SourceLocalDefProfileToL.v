(** An actual Def0 profile is an actual L profile in a hierarchy level.
    This proof uses the fixed L_def theorem and both genuine Ex rules. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalEnvironments
 NumericalSourceFull SourceLocalDefinabilityContext SourceLocalDefinabilityUnpack SourceLocalDefMember SourceNamedVacuity
 SourceNamedQuantifierRules SourceNamedElimination SourceProofWeakening SourceContextProofHelpers SourceConjunctionRules
 SourceUpperProofHelpers SourceOrdinalPredicate SourceHierarchySyntax SourceLFixed NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_full_local_def_profile_to_L M fb fc fn gb gc gn ordinalName A D Y ordinal level predicate member inL
 profile bodyD exD bodyL exL k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 numerical_instantiation M(source_ordinal_predicate_code M)ordinalName ordinal ->source_LL_instance M ordinalName A level ->
 code_relation M(local_def_names A D)source_local_def_predicate_expression predicate ->
 sf_relation M SFMember Y D member ->numerical_instantiation M(source_L_domain_code M)Y inL ->
 sf_relation M SFAnd member profile bodyD ->source_named_quantifier M false Y bodyD exD ->
 sf_relation M SFAnd inL profile bodyL ->source_named_quantifier M false Y bodyL exL ->
 source_named_context_vacuous M gb gc gn Y ->source_bounded M bodyD k ->source_bounded M bodyL k ->
 source_full_prv M gb gc gn ordinal ->source_full_prv M gb gc gn level ->source_full_prv M gb gc gn predicate ->
 source_full_prv M gb gc gn exD ->source_full_prv M gb gc gn exL.
Proof.
 intros HF HI BC HO HL HD HM HIn HBD HED HBL HEL VY BBD BBL PO PL PD PED.
 destruct(environment_cons_total M gb gc gn bodyD)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M gb gc gn bodyD ub uc un k HCons)(conj BBD BC))as BU.
 pose proof(source_full_cons_head M gb gc gn bodyD ub uc un k HCons BBD BU)as PBody.
 pose proof(source_full_conjunction_left M ub uc un member profile bodyD HBD PBody)as PMember.
 pose proof(source_full_conjunction_right M ub uc un member profile bodyD HBD PBody)as PProfile.
 pose proof(source_full_cons_weaken M gb gc gn bodyD ub uc un k ordinal HCons BU PO)as PO'.
 pose proof(source_full_cons_weaken M gb gc gn bodyD ub uc un k level HCons BU PL)as PL'.
 pose proof(source_full_cons_weaken M gb gc gn bodyD ub uc un k predicate HCons BU PD)as PD'.
 assert(HI':context_included M fb fc fn ub uc un).
 { intros f HH. apply(proj2(context_member_cons M gb gc gn bodyD ub uc un f HCons)). right;exact(HI f HH). }
 pose proof(source_full_local_def_member M fb fc fn ub uc un ordinalName A D Y ordinal level predicate member inL k
  HF HI' BU HO HL HD HM HIn PO' PL' PD' PMember)as PInL.
 pose proof(source_full_conjunction M ub uc un inL profile bodyL HBL PInL PProfile)as PBodyL.
 pose proof(source_full_named_quantifier_ex_intro M ub uc un Y bodyL exL HEL PBodyL)as PExL.
 destruct(sf_relation_total M SFImpl bodyD exL)as(point&HPoint).
 pose proof(source_full_implication_intro M gb gc gn bodyD exL point ub uc un HCons HPoint PExL)as PPoint.
 exact(source_full_named_exists_elim M gb gc gn Y bodyD exD exL point VY
  (source_named_quantifier_is_vacuous M false Y bodyL exL k BBL HEL)HED HPoint PPoint PED).
Qed.
Print Assumptions source_full_local_def_profile_to_L.
