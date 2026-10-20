(** Literal ex_cond target and its ordinary source existential introduction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  NumericalRenamingMaps NumericalRenaming SourceUnarySubstitution SourceDomainInstances SourceOrdinalPredicate SourceQuantifierRules SourceRelativizationBounds SourceRenamingIdentity
  SourceReflectionCondition SourceReflectionConditionBounds SourceReflectionConditionTransport SourcePieceConjunctionBounds SubstitutionSource.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_reflection_existence_goal M domain level sb sc n x out:=exists condition body,
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition /\
  sf_relation M SFAnd(source_ordinal_predicate_code M)condition body /\sf_relation M SFEx body(zeroM M)out.

Theorem source_reflection_existence_total M domain level sb sc n x:
  exists out,source_reflection_existence_goal M domain level sb sc n x out.
Proof.
  destruct(source_reflection_condition_total M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)) as(condition&HC).
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)condition) as(body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(out&HE). exists out,condition,body. auto.
Qed.

Theorem source_reflection_existence_bounded M domain level sb sc n x out k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->source_reflection_existence_goal M domain level sb sc n x out ->
  source_bounded M out k.
Proof.
  intros HD HL HV HX(condition&body&HC&HB&HE).
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition(succM M k)
    HD HL(source_ordinal_predicate_bounded M)HV(proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HC) as BC.
  apply(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HE)).
  exact(proj2(source_bounded_accept_binary M SFAnd(source_ordinal_predicate_code M)condition body(succM M k)(or_introl eq_refl)HB)
    (conj(sr_domain_bound_succ M(source_ordinal_predicate_code M)k(source_ordinal_predicate_bounded M))BC)).
Qed.

Theorem source_reflection_existence_renaming M domain level sb sc n x f rb rc rn delta y out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->source_reflection_existence_goal M domain level sb sc n x f ->
  numerical_renaming M f rb rc rn delta out ->renaming_lookup M rb rc rn delta x y ->
  source_reflection_existence_goal M domain level sb sc n y out.
Proof.
  intros HD HL HV(condition&body&HC&HB&HE)HR HX.
  destruct(proj1(numerical_renaming_quantifier M false body f rb rc rn delta out HE)HR)
    as(ab&ac&an&body'&HMap&HRBody&HE').
  destruct(proj1(numerical_renaming_binary M SFAnd(source_ordinal_predicate_code M)condition body ab ac an delta body'
    (or_introl eq_refl)HB)HRBody) as(ord'&condition'&HROrd&HRCondition&HB').
  pose proof(numerical_renaming_lift_fixes_domain M(source_ordinal_predicate_code M)rb rc rn delta ab ac an
    (source_ordinal_predicate_bounded M)HMap) as HOrdSelf.
  pose proof(numerical_renaming_functional M(source_ordinal_predicate_code M)ab ac an delta ord'(source_ordinal_predicate_code M)HROrd HOrdSelf) as E. subst ord'.
  pose proof(source_reflection_condition_renaming M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition
    ab ac an delta(succM M y)(zeroM M)condition' HD HL(source_ordinal_predicate_bounded M)HV HC HRCondition
    (proj2(proj2 HMap)x y HX)(proj1(proj2 HMap))) as HC'.
  exists condition',body'. auto.
Qed.

Theorem source_full_reflection_existence_intro M b c l domain level sb sc n x goal d ordinal condition k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->coding_lt M d k ->context_bounded M b c l k ->
  source_reflection_existence_goal M domain level sb sc n x goal ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n x d condition ->
  source_full_prv M b c l ordinal ->source_full_prv M b c l condition ->source_full_prv M b c l goal.
Proof.
  intros HD HL HV HX HDk HC HGoal HOrd HCondition POrd PCondition.
  pose proof(source_reflection_existence_bounded M domain level sb sc n x goal k HD HL HV HX HGoal) as BGoal.
  destruct HGoal as(oldCondition&body&HOldCondition&HBody&HEx).
  destruct(sf_relation_total M SFAnd ordinal condition) as(instance&HInstance).
  destruct(substitution_singleton_total M d) as(rb&rc&HHead&HTail).
  pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)(zeroM M)(source_ordinal_predicate_code M)
    rb rc(code_numeral M 1)(zeroM M)d ordinal(source_ordinal_predicate_bounded M)
    (source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))HHead HOrd) as HOrdSub.
  destruct(numerical_substitution_total M oldCondition rb rc(code_numeral M 1)(zeroM M)) as(condition'&HConditionSub).
  pose proof(source_reflection_condition_substitution M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)oldCondition
    rb rc(code_numeral M 1)(zeroM M)x d condition' HD HL(source_ordinal_predicate_bounded M)HV HOldCondition HConditionSub
    (substitution_singleton_tail M rb rc x)HHead) as HCondition'.
  pose proof(source_reflection_condition_functional M domain level(source_ordinal_predicate_code M)sb sc n x d condition' condition HCondition' HCondition) as E. subst condition'.
  assert(HInst:numerical_instantiation M body d instance).
  { exists rb,rc. split;[exact HHead|].
    apply(proj2(numerical_substitution_binary M SFAnd(source_ordinal_predicate_code M)oldCondition body rb rc(code_numeral M 1)(zeroM M)
      instance(or_introl eq_refl)HBody)). exists ordinal,condition. auto. }
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k(source_ordinal_predicate_bounded M)HDk HOrd) as BOrd.
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x d condition k
    HD HL(source_ordinal_predicate_bounded M)HV HX HDk HCondition) as BCondition.
  pose proof(proj2(source_bounded_accept_binary M SFAnd ordinal condition instance k(or_introl eq_refl)HInstance)(conj BOrd BCondition)) as BInstance.
  apply(full_source_ExI M b c l body goal d instance(ex_intro _ k(conj BGoal HC)));[|exact HEx|exact HInst].
  exact(full_source_CI M b c l ordinal condition instance(ex_intro _ k(conj BInstance HC))POrd PCondition HInstance).
Qed.

Print Assumptions source_reflection_existence_total.
Print Assumptions source_reflection_existence_bounded.
Print Assumptions source_reflection_existence_renaming.
Print Assumptions source_full_reflection_existence_intro.
