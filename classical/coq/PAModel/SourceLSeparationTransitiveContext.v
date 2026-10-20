(** Construct the exact carrier-transitivity proof from genuine hierarchy
    hypotheses. Its fixed ZFR axiom context is added explicitly. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull ContextCombination SourceTraceBounds
  SourceProofWeakening SourceClosedContextShift SourceDerivedRules SourceZFRProvability NumericalInstantiation
  SourceOrdinalPredicate SourceHierarchySyntax SourceHierarchyTransitiveShell
  SourceCommonLevelAbove SourceRawSubset SourceLSeparationCarrierShell SourcePropositionalRebase.
Unset Implicit Arguments.

Lemma source_lsep_carrier_transitive_subset M trans :
  code_relation M(fun _=>zeroM M)E_L_carrier_transitive trans ->
  source_raw_subset_graph M(code_numeral M 2)(code_numeral M 1)trans.
Proof.
  intro HGraph. unfold E_L_carrier_transitive in HGraph.
  destruct(schema_expression_split M _ _ _ _ trans HGraph) as(point&z&HPoint&HZ&HAll).
  change(z=zeroM M)in HZ. subst z.
  destruct(schema_expression_split M _ _ _ _ point HPoint) as(left&right&HLeft&HRight&HImpl).
  destruct(schema_expression_split M _ _ _ _ left HLeft) as(z&x&HZ&HX&HMemberL).
  change(z=zeroM M)in HZ. change(x=code_numeral M 3)in HX. subst z x.
  destruct(schema_expression_split M _ _ _ _ right HRight) as(z&y&HZ&HY&HMemberR).
  change(z=zeroM M)in HZ. change(y=code_numeral M 2)in HY. subst z y.
  exists left,right,point. repeat split;assumption.
Qed.

Theorem source_full_L_carrier_transitive_context M b c n k d ordinal level member trans :
  context_bounded M b c n k ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_LL_instance M d(code_numeral M 1)level ->
  sf_relation M SFMember(code_numeral M 2)(code_numeral M 1)member ->
  code_relation M(fun _=>zeroM M)E_L_carrier_transitive trans ->
  source_full_prv M b c n ordinal ->source_full_prv M b c n level ->source_full_prv M b c n member ->
  exists ab ac an ub uc un,
    source_zfr_context M ab ac an /\context_union M ab ac an b c n ub uc un /\
    source_full_prv M ub uc un trans.
Proof.
  intros HC HO HL HM HT PO PL PM.
  destruct(source_zfr_hierarchy_element_subset_shell M d(code_numeral M 1)(code_numeral M 2))
    as(ordinal'&level'&member'&subset&t2&t1&law&HO'&HL'&HM'&HS&H2&H1&H0&PLaw).
  pose proof(numerical_instantiation_functional M _ d ordinal ordinal' HO HO')as E. subst ordinal'.
  pose proof(source_LL_instance_functional M d(code_numeral M 1)level level' HL HL')as E. subst level'.
  pose proof(sf_relation_functional M SFMember(code_numeral M 2)(code_numeral M 1)member member' HM HM')as E. subst member'.
  pose proof(source_common_subset_functional M(code_numeral M 2)(code_numeral M 1)subset trans HS
    (source_lsep_carrier_transitive_subset M trans HT))as E. subst subset.
  destruct PLaw as(ab&ac&an&HAC&PLaw).
  destruct(context_union_total M ab ac an b c n)as(ub&uc&un&HUnion).
  pose proof(context_union_left M ab ac an b c n ub uc un HUnion)as HLeft.
  pose proof(context_union_right M ab ac an b c n ub uc un HUnion)as HRight.
  pose proof(context_bounded_monotone M ab ac an(zeroM M)k
    (source_zfr_context_closed M ab ac an HAC)(coding_zero_lt_succ M k))as HA.
  pose proof(source_context_union_bounded M ab ac an b c n ub uc un k HUnion HA HC)as HUC.
  pose proof(source_full_prv_weaken_bounded M ab ac an ub uc un law k PLaw HLeft HUC)as PLaw'.
  pose proof(source_full_prv_weaken_bounded M b c n ub uc un ordinal k PO HRight HUC)as PO'.
  pose proof(source_full_prv_weaken_bounded M b c n ub uc un level k PL HRight HUC)as PL'.
  pose proof(source_full_prv_weaken_bounded M b c n ub uc un member k PM HRight HUC)as PM'.
  pose proof(source_full_modus_ponens M ub uc un ordinal t1 law H0 PLaw' PO')as P1.
  pose proof(source_full_modus_ponens M ub uc un level t2 t1 H1 P1 PL')as P2.
  exists ab,ac,an,ub,uc,un. split;[exact HAC|]. split;[exact HUnion|].
  exact(source_full_modus_ponens M ub uc un member trans t2 H2 P2 PM').
Qed.

Print Assumptions source_lsep_carrier_transitive_subset.
Print Assumptions source_full_L_carrier_transitive_context.
