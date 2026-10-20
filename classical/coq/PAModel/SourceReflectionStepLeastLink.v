(** The body of the canonical least-Cond existence statement is exactly
    the ordinal-step relation, including its candidate Cond insertion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceOrdinalPredicate SourceDomainInstances SourcePieceConjunctionBounds SourceReflectionCondition SourceReflectionConditionTransport
  SourceReflectionStep SourceLeastOrdinalGoal SourceLeastOrdinalShift SourceFiniteCutoffShift NumericalSubstitutionMaps.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_reflection_step_least_link M domain level sb sc n x condition least:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition ->
  source_least_ordinal_graph M condition least ->exists body,
    sf_relation M SFEx body(zeroM M)least /\source_reflection_step M domain level sb sc n(succM M x)(zeroM M)body.
Proof.
  intros HD HL HV HC(inserted&HInserted&HGraph).
  destruct HInserted as(rb&rc&rn&HMap&HS).
  destruct HMap as(ab&ac&an&HBase&HMap). destruct HBase as[-> [-> ->]].
  pose proof(source_reflection_condition_substitution M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition
    rb rc rn(code_numeral M 2)(succM M(succM M x))(zeroM M)inserted HD HL(source_ordinal_predicate_bounded M)HV HC HS
    (proj2(proj2 HMap)x(succM M x)(source_cutoff_shift_base_lookup M x))(proj1(proj2 HMap))) as HInserted.
  destruct(source_least_ordinal_expression_split M condition inserted least HGraph)
    as(body&tag&all&point&neg&member&HEx&HBody&HTag&HAll&HPoint&HMember&HNeg).
  exists body. split;[exact HEx|].
  exists(source_ordinal_predicate_code M),condition,inserted,member,neg,point,all,tag.
  split;[apply source_domain_instance_zero,source_ordinal_predicate_bounded|]. auto 12.
Qed.

Print Assumptions source_reflection_step_least_link.
